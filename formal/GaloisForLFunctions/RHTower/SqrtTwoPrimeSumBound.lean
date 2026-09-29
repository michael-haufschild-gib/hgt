import GaloisForLFunctions.RHTower.SqrtTwoPrimesAboveRational
import GaloisForLFunctions.RHTower.ResidueClassPrimeWindowLowerBound

/-!
# The prime sum over normalized primes of `ℤ[√2]` has exponent below one

There are `κ > 0` and `D` such that, for every finite set `Π` of normalized primes of `ℤ[√2]`
and `1 < σ ≤ 2`:

```text
Σ_{π ∈ Π} ( |N π|^{−σ} · Φ(π) + 2 |N π|^{−2} ) ≤ (1 − κ) · log(1/(σ−1)) + D .
```

Group the primes by the rational prime `p` below them. Each fiber costs at most:
* `p^{−2σ}` for inert `p ≡ 3, 5 (mod 8)`;
* `(2 − η) p^{−σ}` for `p ≡ 1 (mod 8)` with phase `{log p / log r} ∈ [¼, ¾]`;
* `2 p^{−σ}` otherwise.

The sharp residue-class bounds give `Σ_{p ≡ 1, 7 (8)} 2p^{−σ} ≤ log(1/(σ−1)) + O(1)`. The
window lower bound makes the saving `η Σ_{window} p^{−σ} ≥ η c log(1/(σ−1)) − O(1)`.
-/

noncomputable section

namespace RHTower.SqrtTwo

open UniqueFactorizationMonoid

/-- The rational prime below a prime of `ℤ[√2]`. -/
def ratPrime (π : ℤ√2) : ℕ := π.norm.natAbs.minFac

theorem ratPrime_spec {π : ℤ√2} (hπ : Prime π) :
    (ratPrime π).Prime ∧ π ∣ ((ratPrime π : ℕ) : ℤ√2) := by
  obtain ⟨p, hp, hdvd, hN⟩ := exists_rat_prime_below hπ
  have hr : ratPrime π = p := by
    unfold ratPrime
    rcases hN with h | h
    · rw [h]; exact hp.minFac_eq
    · rw [h]
      have h1 : p ^ 2 ≠ 1 := by
        have := hp.two_le; nlinarith
      have hmin := Nat.minFac_prime h1
      exact (Nat.prime_dvd_prime_iff_eq hmin hp).mp (hmin.dvd_of_dvd_pow (Nat.minFac_dvd _))
  rw [hr]; exact ⟨hp, hdvd⟩

theorem mem_normalizedFactors_ratPrime {π : ℤ√2} (hπ : Prime π) (hn : normalize π = π) :
    π ∈ normalizedFactors ((ratPrime π : ℕ) : ℤ√2) := by
  obtain ⟨hp, hdvd⟩ := ratPrime_spec hπ
  exact mem_normalizedFactors_of_dvd hπ hn (by exact_mod_cast hp.ne_zero) hdvd

/-- The window condition on a rational prime. -/
def InWindow (p : ℕ) : Prop :=
  p % 8 = 1 ∧ 1 / 4 ≤ Int.fract (Real.log p / Real.log rr) ∧
    Int.fract (Real.log p / Real.log rr) ≤ 3 / 4

instance : DecidablePred InWindow := fun _ => Classical.propDecidable _

/-- The per-prime bound. -/
def primeBound (σ : ℝ) (p : ℕ) : ℝ :=
  if p % 8 = 3 ∨ p % 8 = 5 then (p : ℝ) ^ (-(2 * σ))
  else if InWindow p then (2 - etaW) * (p : ℝ) ^ (-σ) else 2 * (p : ℝ) ^ (-σ)

theorem sum_fiber_le_primeBound {p : ℕ} (hp : p.Prime) (T : Finset (ℤ√2))
    (hT : ∀ π ∈ T, π ∈ normalizedFactors (p : ℤ√2)) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π ≤ primeBound σ p := by
  haveI := Fact.mk hp
  unfold primeBound
  split_ifs with h8 hw
  · exact sum_le_inert h8 T hT σ
  · exact sum_le_split hp T hT hσ (by linarith [hw.2.1]) hw.2.2
  · exact sum_le_two_mul hp T hT hσ

theorem sum_fiber_inv_sq_le {p : ℕ} (hp : p.Prime) (T : Finset (ℤ√2))
    (hT : ∀ π ∈ T, π ∈ normalizedFactors (p : ℤ√2)) :
    ∑ π ∈ T, 2 * ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ 8 * (p : ℝ) ^ (-(2 : ℝ)) := by
  have h := sum_le_two_mul hp T hT (σ := 2) (by norm_num)
  calc ∑ π ∈ T, 2 * ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ))
      ≤ ∑ π ∈ T, 4 * (((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)) * phiW π) := by
        refine Finset.sum_le_sum fun π _ => ?_
        have : (1 / 2 : ℝ) ≤ phiW π := le_max_left _ _
        have : 0 ≤ ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
        nlinarith
    _ = 4 * ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)) * phiW π := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 * (p : ℝ) ^ (-(2 : ℝ))) := by gcongr
    _ = 8 * (p : ℝ) ^ (-(2 : ℝ)) := by ring

/-- `Σ_{p < Y prime} p^{−2} ≤ 1`. -/
theorem sum_prime_inv_sq_le_one (Y : ℕ) :
    ∑ p ∈ (Finset.range Y).filter Nat.Prime, (p : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
  refine le_trans ?_ (ResidueClassPrimes.sum_Ico_inv_mul_pred_le_one Y)
  have hsub : (Finset.range Y).filter Nat.Prime ⊆ Finset.Ico 2 Y := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_Ico.mpr ⟨hp.2.two_le, hp.1⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    Real.rpow_nonneg (Nat.cast_nonneg n) _) (Finset.sum_le_sum fun n hn => ?_)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
  rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
  apply inv_anti₀ (by nlinarith)
  nlinarith


/-- Primes `≢ 3, 5 (mod 8)` are `2` or `≡ 1, 7 (mod 8)`. -/
theorem mod_eight_cases {p : ℕ} (hp : p.Prime) (h : ¬ (p % 8 = 3 ∨ p % 8 = 5)) :
    p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7 := by
  rcases hp.eq_two_or_odd with h2 | hodd
  · exact Or.inl h2
  · right; omega

theorem totient_eight : (Nat.totient 8 : ℝ) = 4 := by
  have : Nat.totient 8 = 4 := by decide
  rw [this]; norm_num

/-- Pointwise decomposition of the per-prime bound. -/
theorem primeBound_le {σ : ℝ} {p : ℕ} (hp : p.Prime) :
    primeBound σ p ≤ (if p % 8 = 3 ∨ p % 8 = 5 then (p : ℝ) ^ (-(2 * σ)) else 0) +
      (if p % 8 = 1 then 2 * (p : ℝ) ^ (-σ) else 0) + (if p % 8 = 7 then 2 * (p : ℝ) ^ (-σ) else 0) +
      (if p = 2 then 2 * (p : ℝ) ^ (-σ) else 0) - etaW * (if InWindow p then (p : ℝ) ^ (-σ) else 0) := by
  unfold primeBound
  by_cases h8 : p % 8 = 3 ∨ p % 8 = 5
  · have hw : ¬ InWindow p := fun hw => by rcases h8 with h | h <;> rw [hw.1] at h <;> omega
    have h1 : ¬ p % 8 = 1 := by rcases h8 with h | h <;> omega
    have h7 : ¬ p % 8 = 7 := by rcases h8 with h | h <;> omega
    have h2 : p ≠ 2 := by rintro rfl; rcases h8 with h | h <;> norm_num at h
    rw [if_pos h8, if_pos h8, if_neg h1, if_neg h7, if_neg h2, if_neg hw]; ring_nf; rfl
  · rw [if_neg h8, if_neg h8]
    by_cases hw : InWindow p
    · have h1 : p % 8 = 1 := hw.1
      have h7 : ¬ p % 8 = 7 := by omega
      have h2 : p ≠ 2 := by rintro rfl; norm_num at h1
      rw [if_pos hw, if_pos hw, if_pos h1, if_neg h7, if_neg h2]
      linarith
    · rw [if_neg hw, if_neg hw]
      rcases mod_eight_cases hp h8 with h2 | h1 | h7
      · subst h2; norm_num
      · have h7 : ¬ p % 8 = 7 := by omega
        have h2 : p ≠ 2 := by rintro rfl; norm_num at h1
        rw [if_pos h1, if_neg h7, if_neg h2]; linarith
      · have h1 : ¬ p % 8 = 1 := by omega
        have h2 : p ≠ 2 := by rintro rfl; norm_num at h7
        rw [if_neg h1, if_pos h7, if_neg h2]; linarith

/-- **The prime sum has logarithmic exponent below one.** -/
theorem exists_prime_sum_bound :
    ∃ κ : ℝ, 0 < κ ∧ ∃ D : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ Ps : Finset (ℤ√2),
      (∀ π ∈ Ps, Prime π ∧ normalize π = π) →
      ∑ π ∈ Ps, (((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π +
          2 * ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤
        (1 - κ) * Real.log (1 / (σ - 1)) + D := by
  classical
  obtain ⟨C₁, hC₁⟩ := ResidueClassPrimes.exists_sum_prime_rpow_le (q := 8) (a := 1)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₇, hC₇⟩ := ResidueClassPrimes.exists_sum_prime_rpow_le (q := 8) (a := 7)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨cB, hcB, CB, hB⟩ := ResidueClassPrimes.exists_window_prime_sum_lower (q := 8) (a := 1)
    (by norm_num) (by norm_num) (by norm_num) one_lt_rr
  refine ⟨etaW * cB, mul_pos etaW_pos hcB, 2 * C₁ + 2 * C₇ + 10 + etaW * CB,
    fun σ hσ hσ2 Ps hPs => ?_⟩
  set L := Real.log (1 / (σ - 1)) with hL
  obtain ⟨Y₀, hY₀⟩ := hB σ hσ hσ2
  set P := Ps.image ratPrime with hP
  set Y := max Y₀ (P.sup id + 1) with hY
  set Q := (Finset.range Y).filter Nat.Prime with hQ
  have hmaps : ∀ π ∈ Ps, ratPrime π ∈ P := fun π hπ => Finset.mem_image_of_mem _ hπ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ p ∈ P, ∑ π ∈ Ps with ratPrime π = p,
      (((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π + 2 * ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤
        primeBound σ p + 8 * (p : ℝ) ^ (-(2 : ℝ)) := by
    intro p hp
    obtain ⟨π₀, hπ₀, rfl⟩ := Finset.mem_image.mp hp
    have hpprime := (ratPrime_spec (hPs π₀ hπ₀).1).1
    have hT : ∀ π ∈ Ps.filter (fun π => ratPrime π = ratPrime π₀),
        π ∈ normalizedFactors ((ratPrime π₀ : ℕ) : ℤ√2) := by
      intro π hπ
      obtain ⟨hπPs, heq⟩ := Finset.mem_filter.mp hπ
      rw [← heq]; exact mem_normalizedFactors_ratPrime (hPs π hπPs).1 (hPs π hπPs).2
    rw [Finset.sum_add_distrib]
    exact add_le_add (sum_fiber_le_primeBound hpprime _ hT (by linarith))
      (sum_fiber_inv_sq_le hpprime _ hT)
  have hPQ : P ⊆ Q := by
    intro p hp
    obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hp
    rw [hQ, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, (ratPrime_spec (hPs π hπ).1).1⟩
    have : ratPrime π ≤ P.sup id := Finset.le_sup (f := id) hp
    omega
  have hnonneg : ∀ p : ℕ, 0 ≤ primeBound σ p + 8 * (p : ℝ) ^ (-(2 : ℝ)) := by
    intro p
    have h8 : 0 ≤ 8 * (p : ℝ) ^ (-(2 : ℝ)) := by positivity
    have hb : 0 ≤ primeBound σ p := by
      unfold primeBound
      have := etaW_le_half
      split_ifs
      · positivity
      · exact mul_nonneg (by linarith) (by positivity)
      · positivity
    linarith
  -- the class sums
  have hs1 := hC₁ σ hσ hσ2 (Finset.range Y)
  have hs7 := hC₇ σ hσ hσ2 (Finset.range Y)
  rw [totient_eight] at hs1 hs7
  have hwin := hY₀ Y (le_max_left _ _)
  have hsq := sum_prime_inv_sq_le_one Y
  have h2σ : (2 : ℝ) ^ (-σ) ≤ 1 / 2 := by
    calc (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  -- the four indicator sums over `Q`
  set A35 := ∑ p ∈ Q, (if p % 8 = 3 ∨ p % 8 = 5 then (p : ℝ) ^ (-(2 * σ)) else 0) with hA35
  set A1 := ∑ p ∈ Q, (if p % 8 = 1 then 2 * (p : ℝ) ^ (-σ) else 0) with hA1
  set A7 := ∑ p ∈ Q, (if p % 8 = 7 then 2 * (p : ℝ) ^ (-σ) else 0) with hA7
  set A2 := ∑ p ∈ Q, (if p = 2 then 2 * (p : ℝ) ^ (-σ) else 0) with hA2
  set AW := ∑ p ∈ Q, (if InWindow p then (p : ℝ) ^ (-σ) else 0) with hAW
  have hdec : ∑ p ∈ Q, primeBound σ p ≤ A35 + A1 + A7 + A2 - etaW * AW := by
    refine (Finset.sum_le_sum fun p hp => primeBound_le (Finset.mem_filter.mp hp).2).trans
      (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have h35 : A35 ≤ 1 := by
    rw [hA35, ← Finset.sum_filter]
    refine le_trans ?_ hsq
    refine le_trans (Finset.sum_le_sum fun p hp => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ Q)
        fun p _ _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    have hp2 : (1 : ℝ) ≤ p := by
      have := ((Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2).two_le
      exact_mod_cast (by omega : 1 ≤ p)
    exact Real.rpow_le_rpow_of_exponent_le hp2 (by linarith)
  have h1 : A1 ≤ 2 * (1 / 4 * Real.log (1 / (σ - 1)) + C₁) := by
    rw [hA1, ← Finset.sum_filter, ← Finset.mul_sum]
    have : Q.filter (fun p => p % 8 = 1) =
        (Finset.range Y).filter (fun p : ℕ => p.Prime ∧ p % 8 = 1) := by
      rw [hQ, Finset.filter_filter]
    rw [this]; linarith
  have h7 : A7 ≤ 2 * (1 / 4 * Real.log (1 / (σ - 1)) + C₇) := by
    rw [hA7, ← Finset.sum_filter, ← Finset.mul_sum]
    have : Q.filter (fun p => p % 8 = 7) =
        (Finset.range Y).filter (fun p : ℕ => p.Prime ∧ p % 8 = 7) := by
      rw [hQ, Finset.filter_filter]
    rw [this]; linarith
  have h2 : A2 ≤ 1 := by
    rw [hA2, ← Finset.sum_filter]
    have hsub : Q.filter (fun p => p = 2) ⊆ {2} := by
      intro p hp; simp only [Finset.mem_filter] at hp; simp [hp.2]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity) ?_
    simp only [Finset.sum_singleton]; push_cast; linarith
  have hW : cB * Real.log (1 / (σ - 1)) - CB ≤ AW := by
    rw [hAW, ← Finset.sum_filter]
    have : Q.filter InWindow = (Finset.range Y).filter (fun p : ℕ => p.Prime ∧ p % 8 = 1 ∧
        1 / 4 ≤ Int.fract (Real.log (p : ℝ) / Real.log rr) ∧
          Int.fract (Real.log (p : ℝ) / Real.log rr) ≤ 3 / 4) := by
      ext p
      simp only [hQ, Finset.mem_filter, InWindow]
      tauto
    rw [this]; exact hwin
  have h8sum : ∑ p ∈ Q, 8 * (p : ℝ) ^ (-(2 : ℝ)) ≤ 8 := by
    rw [← Finset.mul_sum]; linarith
  calc ∑ p ∈ P, ∑ π ∈ Ps with ratPrime π = p,
        (((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π + 2 * ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)))
      ≤ ∑ p ∈ P, (primeBound σ p + 8 * (p : ℝ) ^ (-(2 : ℝ))) := Finset.sum_le_sum hfib
    _ ≤ ∑ p ∈ Q, (primeBound σ p + 8 * (p : ℝ) ^ (-(2 : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hPQ fun p _ _ => hnonneg p
    _ = ∑ p ∈ Q, primeBound σ p + ∑ p ∈ Q, 8 * (p : ℝ) ^ (-(2 : ℝ)) := Finset.sum_add_distrib
    _ ≤ (1 - etaW * cB) * L + (2 * C₁ + 2 * C₇ + 10 + etaW * CB) := by
        have hη := etaW_pos
        have hηW : etaW * (cB * L - CB) ≤ etaW * AW := mul_le_mul_of_nonneg_left hW hη.le
        nlinarith

end RHTower.SqrtTwo
