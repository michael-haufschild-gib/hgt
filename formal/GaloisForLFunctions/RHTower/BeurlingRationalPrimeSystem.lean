import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.HTGeometry.BeurlingCrossSystemBlindness

/-!
# The rational primes and the generator swap as Beurling systems

Two Beurling systems on the index type `ℕ`, carrying the same magnitudes `max n 1`.

* `rationalPrimeSystem` gives atom `n` the weight `Λ(n)/n`; Mertens' first theorem in von Mangoldt
  form says its Mertens sum stays within a constant of `log x`.
* `swappedPrimeSystem` deletes the powers of the generator `2` and doubles the powers of `3`.  Each
  generator contributes a geometric tail of total mass at most `log q`, so the swap moves the
  Mertens sum by a bounded amount and the swapped system is Mertens-normal too.

The two systems therefore satisfy the hypotheses of the cross-system blindness theorem, while their
zeta functions have different zero sets.
-/

open ArithmeticFunction GaloisForLFunctions.HTGeometry.Beurling

namespace RHTower

/-! ### Geometric tails of one generator -/

theorem sum_inv_pow_le {q : ℝ} (hq : 2 ≤ q) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (q ^ k)⁻¹ ≤ 1 - (q ^ K)⁻¹ := by
  have hq0 : (0 : ℝ) < q := by linarith
  induction K with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hpow : (0 : ℝ) < q ^ M := by positivity
    have hkey : 2 * (q ^ (M + 1))⁻¹ ≤ (q ^ M)⁻¹ := by
      rw [pow_succ, mul_inv, ← sub_nonneg]
      have hrw : (q ^ M)⁻¹ - 2 * ((q ^ M)⁻¹ * q⁻¹) = (q ^ M)⁻¹ * (1 - 2 * q⁻¹) := by ring
      rw [hrw]
      have hinv : q⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ hq0 (by norm_num)]
        linarith
      exact mul_nonneg (by positivity) (by linarith)
    linarith [ih, hkey]

/-- The atoms of the generator `q`: its powers `q^k` with `k ≥ 1`. -/
def IsGenPow (q n : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ n = q ^ k

noncomputable instance IsGenPow.instDecidable (q n : ℕ) : Decidable (IsGenPow q n) :=
  Classical.dec _

/-- **A generator's total Mertens mass is at most `log q`.**  Its atoms `q^k` all carry the weight
`Λ(q) ≤ log q` and the magnitudes grow geometrically. -/
theorem genPow_tail_le {q : ℕ} (hq : 2 ≤ q) (K : ℕ) :
    ∑ n ∈ (Finset.range (K + 1)).filter (fun n => IsGenPow q n), (Λ n : ℝ) / n
      ≤ Real.log q := by
  classical
  have hq1 : 1 < q := by omega
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hsubset : (Finset.range (K + 1)).filter (fun n => IsGenPow q n)
      ⊆ (Finset.Icc 1 K).image (fun k => q ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨k, hk1, hk⟩ := hn.2
    refine Finset.mem_image.mpr ⟨k, ?_, hk.symm⟩
    rw [Finset.mem_Icc]
    refine ⟨hk1, ?_⟩
    have hklt : k < q ^ k := Nat.lt_pow_self hq1
    omega
  have hnonneg : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) / n :=
    fun n => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hinj : Set.InjOn (fun k => q ^ k) (Finset.Icc 1 K : Finset ℕ) := by
    intro a _ b _ hab
    exact Nat.pow_right_injective hq hab
  have hstep1 : ∑ n ∈ (Finset.range (K + 1)).filter (fun n => IsGenPow q n), (Λ n : ℝ) / n
      ≤ ∑ n ∈ (Finset.Icc 1 K).image (fun k => q ^ k), (Λ n : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => hnonneg m)
  have hstep2 : ∑ n ∈ (Finset.Icc 1 K).image (fun k => q ^ k), (Λ n : ℝ) / n
      = ∑ k ∈ Finset.Icc 1 K, (Λ (q ^ k) : ℝ) / ((q ^ k : ℕ) : ℝ) := Finset.sum_image hinj
  have hstep3 : ∑ k ∈ Finset.Icc 1 K, (Λ (q ^ k) : ℝ) / ((q ^ k : ℕ) : ℝ)
      = (Λ q : ℝ) * ∑ k ∈ Finset.Icc 1 K, ((q : ℝ) ^ k)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    rw [vonMangoldt_apply_pow (by omega : k ≠ 0), Nat.cast_pow]
    ring
  have hgeom : ∑ k ∈ Finset.Icc 1 K, ((q : ℝ) ^ k)⁻¹ ≤ 1 := by
    have := sum_inv_pow_le hqR K
    have hpos : (0 : ℝ) < ((q : ℝ) ^ K)⁻¹ := by positivity
    linarith
  calc ∑ n ∈ (Finset.range (K + 1)).filter (fun n => IsGenPow q n), (Λ n : ℝ) / n
      ≤ (Λ q : ℝ) * ∑ k ∈ Finset.Icc 1 K, ((q : ℝ) ^ k)⁻¹ := by
        rw [← hstep3, ← hstep2]; exact hstep1
    _ ≤ (Λ q : ℝ) * 1 := mul_le_mul_of_nonneg_left hgeom vonMangoldt_nonneg
    _ = (Λ q : ℝ) := mul_one _
    _ ≤ Real.log q := vonMangoldt_le_log

/-! ### The two systems -/

theorem primeSystem_finite_below (x : ℝ) : {n : ℕ | max (n : ℝ) 1 ≤ x}.Finite := by
  refine Set.Finite.subset (Set.finite_Iic ⌊x⌋₊) ?_
  intro n hn
  have hnx : (n : ℝ) ≤ x := le_trans (le_max_left _ _) hn
  exact Nat.le_floor hnx

/-- The rational primes as a Beurling system. -/
noncomputable def rationalPrimeSystem : System ℕ where
  mag n := max (n : ℝ) 1
  weight n := (Λ n : ℝ) / n
  one_le_mag _ := le_max_right _ _
  weight_nonneg n := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  finite_below := primeSystem_finite_below

/-- The weight of the system obtained by deleting the generator `2` and adjoining a second copy of
the generator `3`. -/
noncomputable def swapWeight (n : ℕ) : ℝ :=
  if IsGenPow 2 n then 0
    else if IsGenPow 3 n then 2 * ((Λ n : ℝ) / n)
    else (Λ n : ℝ) / n

theorem swapWeight_nonneg (n : ℕ) : 0 ≤ swapWeight n := by
  rw [swapWeight]
  split_ifs with h2 h3
  · exact le_rfl
  · exact mul_nonneg (by norm_num) (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n))
  · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

/-- The rational primes with the generator `2` replaced by a second copy of `3`. -/
noncomputable def swappedPrimeSystem : System ℕ where
  mag n := max (n : ℝ) 1
  weight := swapWeight
  one_le_mag _ := le_max_right _ _
  weight_nonneg := swapWeight_nonneg
  finite_below := primeSystem_finite_below

theorem swapped_aperture_eq (x : ℝ) :
    swappedPrimeSystem.aperture x = rationalPrimeSystem.aperture x := rfl

theorem aperture_eq_range {x : ℝ} (hx : 1 ≤ x) :
    rationalPrimeSystem.aperture x = Finset.range (⌊x⌋₊ + 1) := by
  ext n
  rw [System.mem_aperture, Finset.mem_range]
  constructor
  · intro h
    have hnx : (n : ℝ) ≤ x := le_trans (le_max_left _ _) h
    exact Nat.lt_succ_of_le (Nat.le_floor hnx)
  · intro h
    have hn : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp h
    have hnx : (n : ℝ) ≤ x :=
      le_trans (Nat.cast_le.mpr hn) (Nat.floor_le (by linarith))
    exact max_le hnx hx

/-! ### Mertens-normality of both systems -/

theorem rationalPrimeSystem_mertens {x : ℝ} (hx : 1 ≤ x) :
    rationalPrimeSystem.mertens x = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (Λ d : ℝ) / d := by
  have hK : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hmert : rationalPrimeSystem.mertens x
      = ∑ n ∈ rationalPrimeSystem.aperture x, (Λ n : ℝ) / n := rfl
  rw [hmert, aperture_eq_range hx, hK, Finset.sum_insert (by simp)]
  simp

theorem log_two_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)

theorem log_three_nonneg : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)

/-- Rounding the aperture down to an integer moves the logarithm by at most `log 2`. -/
theorem abs_log_sub_log_floor_le {x : ℝ} (hx : 1 ≤ x) :
    |Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| ≤ Real.log 2 := by
  have hfloor1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hR1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor1
  have hpos : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hle2 : x ≤ 2 * ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hlow : 0 ≤ Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hpos hle)
  have hhigh : Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < x) hle2
    rw [Real.log_mul (by norm_num) (ne_of_gt hpos)] at h
    linarith
  rw [abs_le]
  exact ⟨by linarith [log_two_nonneg], hhigh⟩

/-- **The rational primes are Mertens-normal**, by Mertens' first theorem in von Mangoldt form. -/
theorem exists_rationalPrimeSystem_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 1 ≤ x →
      |rationalPrimeSystem.mertens x - Real.log x - 0| ≤ M := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨(Real.log 4 + 4) + Real.log 2, by linarith [log_two_nonneg], fun x hx => ?_⟩
  have hfloor1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hbase := Mertens.mertens_first ⌊x⌋₊ hfloor1
  have hlog := abs_log_sub_log_floor_le hx
  rw [rationalPrimeSystem_mertens hx, sub_zero]
  calc |(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (Λ d : ℝ) / d) - Real.log x|
      ≤ |(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (Λ d : ℝ) / d) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)|
        + |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := abs_sub_le _ _ _
    _ ≤ (Real.log 4 + 4) + Real.log 2 := by
        rw [abs_sub_comm (Real.log ((⌊x⌋₊ : ℕ) : ℝ))]
        exact add_le_add hbase hlog

theorem swapped_mertens_sub (x : ℝ) :
    swappedPrimeSystem.mertens x - rationalPrimeSystem.mertens x
      = ∑ n ∈ rationalPrimeSystem.aperture x, (swapWeight n - (Λ n : ℝ) / n) := by
  have h1 : swappedPrimeSystem.mertens x
      = ∑ n ∈ rationalPrimeSystem.aperture x, swapWeight n := rfl
  have h2 : rationalPrimeSystem.mertens x
      = ∑ n ∈ rationalPrimeSystem.aperture x, (Λ n : ℝ) / n := rfl
  rw [h1, h2, ← Finset.sum_sub_distrib]

/-- The swap moves each atom's weight by at most the two generator indicators. -/
theorem abs_swapWeight_sub_le (n : ℕ) :
    |swapWeight n - (Λ n : ℝ) / n|
      ≤ (if IsGenPow 2 n then (Λ n : ℝ) / n else 0)
        + (if IsGenPow 3 n then (Λ n : ℝ) / n else 0) := by
  have hnn : 0 ≤ (Λ n : ℝ) / n := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  rw [swapWeight]
  by_cases h2 : IsGenPow 2 n
  · rw [if_pos h2, if_pos h2, zero_sub, abs_neg, abs_of_nonneg hnn]
    split_ifs <;> linarith
  · rw [if_neg h2, if_neg h2]
    by_cases h3 : IsGenPow 3 n
    · rw [if_pos h3, if_pos h3,
        show 2 * ((Λ n : ℝ) / n) - (Λ n : ℝ) / n = (Λ n : ℝ) / n by ring, abs_of_nonneg hnn]
      linarith
    · rw [if_neg h3, if_neg h3, sub_self, abs_zero]
      linarith

/-- **The generator swap keeps the system Mertens-normal.**  The two corrections are the geometric
tails of the generators `2` and `3`, each of mass at most `log q`. -/
theorem exists_swappedPrimeSystem_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 1 ≤ x →
      |swappedPrimeSystem.mertens x - Real.log x - 0| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_rationalPrimeSystem_bound
  refine ⟨M + (Real.log 2 + Real.log 3),
    by linarith [log_two_nonneg, log_three_nonneg], fun x hx => ?_⟩
  have hbase : |rationalPrimeSystem.mertens x - Real.log x| ≤ M := by
    have h := hM x hx
    rwa [sub_zero] at h
  have hdiff : |swappedPrimeSystem.mertens x - rationalPrimeSystem.mertens x|
      ≤ Real.log 2 + Real.log 3 := by
    rw [swapped_mertens_sub, aperture_eq_range hx]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun m _ => abs_swapWeight_sub_le m) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    exact add_le_add (genPow_tail_le (by norm_num) ⌊x⌋₊) (genPow_tail_le (by norm_num) ⌊x⌋₊)
  rw [sub_zero]
  calc |swappedPrimeSystem.mertens x - Real.log x|
      ≤ |swappedPrimeSystem.mertens x - rationalPrimeSystem.mertens x|
        + |rationalPrimeSystem.mertens x - Real.log x| := abs_sub_le _ _ _
    _ ≤ (Real.log 2 + Real.log 3) + M := add_le_add hdiff hbase
    _ = M + (Real.log 2 + Real.log 3) := by ring

/-! ### The blindness statement for the concrete pair -/

/-- **Theorem 3.2.**  Two Mertens-normal Beurling systems — the rational primes, and the rational
primes with the generator `2` replaced by a second copy of `3` — on which every multiplicative
regularization that converges takes the same limit, while their zeta functions have different zero
sets: `s₀ = 2πi/log 2` is a zero of the swapped system's zeta function, is not a pole of its
generator-`3` factor, and is not a zero of `ζ`. -/
theorem rationalPrime_swap_blindness (k : ℕ) (c : ℝ → ℝ) (ℓ ℓ' : ℝ)
    (hc : Filter.Tendsto (fun N => c N * rationalPrimeSystem.jet k N) Filter.atTop (nhds ℓ))
    (hc' : Filter.Tendsto (fun N => c N * swappedPrimeSystem.jet k N) Filter.atTop (nhds ℓ')) :
    ℓ = ℓ' ∧ swappedZeta genFreq = 0 ∧ riemannZeta genFreq ≠ 0 := by
  obtain ⟨M, -, hM⟩ := exists_rationalPrimeSystem_bound
  obtain ⟨M', -, hM'⟩ := exists_swappedPrimeSystem_bound
  exact ⟨regularized_jet_limit_eq_of_systems rationalPrimeSystem swappedPrimeSystem hM hM' k hc hc',
    swappedZeta_genFreq, riemannZeta_genFreq_ne_zero⟩

end RHTower
