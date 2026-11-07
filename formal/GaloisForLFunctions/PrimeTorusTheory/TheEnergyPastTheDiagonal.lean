import GaloisForLFunctions.PrimeTorusTheory.TheDiagonalRange
import GaloisForLFunctions.PrimeTorusTheory.TheOrbitEscapesProgressions

/-!
# The energy past the diagonal

Through the diagonal range the near-diagonal energy is diagonal (`energy_le`). Past it `k`-fold products of primes overflow the boxes of width `1/H`, and
interpolation gives only `E_{k+1} ≤ S² E_k` (`clockedMoment_succ_le`). Here is what is known at every `k`.

**Theorem** (`energy_le_past_diagonal`). At weights `a_r = r^{−σ}`, `σ ≥ 0`, on any set `Q` of primes, for all `k` and all `H > 0`,

`E_k(H) ≤ k! (Σ_r r^{−2σ})^k + 24 k! (Σ_r r^{1−2σ})^k / H + 32 S^{2k} / H²`.

**Mechanism.** A fibre of the product has at most `k!` tuples, of weight `n^{−σ}`. The kernel `sinc²(H log(n/m)/2)` over the integers `n` near `m` has total mass `≲ m/H`,
whichever integers occur. So the near-diagonal count is bounded by treating every integer in the interval as a product of `k` primes.

At `σ = ½` the middle term is `k! π(y)^k/H`, and it lies within `k! (log y/4)^k · 8kΛ` of the lower bound `S^{2k}/(8kΛH)` (`energy_ge_start`). The remaining gap is exactly the density of
`y`-smooth numbers in the interval, `≈ 1/(k log y)^k`: this is what the true count would save, and what no available estimate sees.

It beats interpolation from the diagonal range `k₀ = log H/log y` for `k` up to `k₀ (1 + log log y/log k₀)`, and it holds with no restriction on `H` against `k`, so it gives a count of large values at every
scale (`card_largeValue_le_past_diagonal`). The middle term is independent of the window: `R ≪ kΛ k! (π(y)/(θS)²)^k/θ` for every `H`.

**The oscillating energy.** Every absolute bound is at least `S^{2k}/(8kΛH)`, so the positive energy never sees a saving. The oscillating energy is the clocked moment, and so it is bounded by the supremum of the modulus
on the window (`shiftedEnergy_le_of_norm_le`). With the rotation-proof saving this gives `E^{T}_k ≤ (S − c L^{−19} ℓ^{−14})^{2k}` for all `k` and `H ≤ T/2` (`shiftedEnergy_critical_le`). This is the first bound for the
oscillating energy that is below the positive energy at any height: it separates them once `k ≫ S L^{19} ℓ^{14} log(kΛH)`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- `Σ_{c < h ≤ c + N} 1/h² ≤ 1/c − 1/(c + N)`. -/
theorem sum_Ioc_inv_sq_le {c : ℕ} (hc : 1 ≤ c) (N : ℕ) :
    ∑ h ∈ Finset.Ioc c (c + N), 1 / (h : ℝ) ^ 2 ≤ 1 / (c : ℝ) - 1 / ((c + N : ℕ) : ℝ) := by
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc
  induction N with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega)]
    have hn : (0 : ℝ) < ((c + n : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have key : 1 / (((c + n + 1 : ℕ) : ℝ)) ^ 2 ≤
        1 / ((c + n : ℕ) : ℝ) - 1 / ((c + n + 1 : ℕ) : ℝ) := by
      have e : ((c + n + 1 : ℕ) : ℝ) = ((c + n : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      rw [e, div_sub_div _ _ hn.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- **The mass of the near-diagonal kernel.** `Σ_{h ≥ 1} min(1, X²/h²) ≤ 3X`. -/
theorem sum_min_le {X : ℝ} (hX : 0 < X) (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, min 1 (X ^ 2 / (h : ℝ) ^ 2) ≤ 3 * X := by
  have hterm : ∀ h : ℕ, min 1 (X ^ 2 / (h : ℝ) ^ 2) ≤ X ^ 2 * (1 / (h : ℝ) ^ 2) := fun h => by
    rw [mul_one_div]
    exact min_le_right _ _
  have hnn : ∀ h : ℕ, 0 ≤ min 1 (X ^ 2 / (h : ℝ) ^ 2) := fun h =>
    le_min zero_le_one (by positivity)
  rcases lt_or_ge X 1 with hlt | hge
  · calc _ ≤ ∑ h ∈ Finset.Icc 1 N, X ^ 2 * (1 / (h : ℝ) ^ 2) := Finset.sum_le_sum fun h _ => hterm h
      _ = X ^ 2 * ∑ h ∈ Finset.Icc 1 N, 1 / (h : ℝ) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ X ^ 2 * 2 := mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le N) (by positivity)
      _ ≤ 3 * X := by nlinarith
  · set c := ⌊X⌋₊ with hc
    have hc1 : 1 ≤ c := Nat.le_floor (by exact_mod_cast hge)
    have hcr : (c : ℝ) ≤ X := Nat.floor_le hX.le
    have hc2 : X < (c : ℝ) + 1 := Nat.lt_floor_add_one X
    have hcr1 : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 c ∪ Finset.Ioc c (c + N) := by
      intro h hh
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hh
      rcases le_or_gt h c with hle | hgt
      · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨h1, hle⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨hgt, by omega⟩)
    have hdisj : Disjoint (Finset.Icc 1 c) (Finset.Ioc c (c + N)) := by
      rw [Finset.disjoint_left]
      intro h h1 h2
      have := (Finset.mem_Icc.mp h1).2
      have := (Finset.mem_Ioc.mp h2).1
      omega
    have h1 : ∑ h ∈ Finset.Icc 1 c, min 1 (X ^ 2 / (h : ℝ) ^ 2) ≤ X := by
      calc _ ≤ ∑ _h ∈ Finset.Icc 1 c, (1 : ℝ) := Finset.sum_le_sum fun h _ => min_le_left _ _
        _ = c := by simp
        _ ≤ X := hcr
    have h2 : ∑ h ∈ Finset.Ioc c (c + N), min 1 (X ^ 2 / (h : ℝ) ^ 2) ≤ 2 * X := by
      calc _ ≤ ∑ h ∈ Finset.Ioc c (c + N), X ^ 2 * (1 / (h : ℝ) ^ 2) :=
            Finset.sum_le_sum fun h _ => hterm h
        _ = X ^ 2 * ∑ h ∈ Finset.Ioc c (c + N), 1 / (h : ℝ) ^ 2 := (Finset.mul_sum _ _ _).symm
        _ ≤ X ^ 2 * (1 / (c : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h3 := sum_Ioc_inv_sq_le hc1 N
            have h4 : (0 : ℝ) ≤ 1 / ((c + N : ℕ) : ℝ) := by positivity
            linarith
        _ ≤ 2 * X := by
            rw [mul_one_div, div_le_iff₀ (by linarith)]
            nlinarith
    calc _ ≤ ∑ h ∈ Finset.Icc 1 c ∪ Finset.Ioc c (c + N), min 1 (X ^ 2 / (h : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ => hnn h
      _ = _ := Finset.sum_union hdisj
      _ ≤ 3 * X := by linarith

theorem sinc_sq_le_one (x : ℝ) : Real.sinc x ^ 2 ≤ 1 :=
  (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨Real.neg_one_le_sinc x, Real.sinc_le_one x⟩)

/-- The clock kernel on a near pair of integers. -/
theorem sinc_sq_near_le {m n : ℕ} (hm : 0 < m) (hmn : m < n) (hn : n < 2 * m) {H : ℝ} (hH : 0 < H) :
    Real.sinc (H * (Real.log m - Real.log n) / 2) ^ 2 ≤
      min 1 ((4 * (m : ℝ) / H) ^ 2 / (((n - m : ℕ) : ℝ)) ^ 2) := by
  refine le_min (sinc_sq_le_one _) ?_
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (hm.trans hmn)
  have hh : (((n - m : ℕ) : ℝ)) = (n : ℝ) - m := by
    rw [Nat.cast_sub hmn.le]
  have hhpos : (0 : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hnle : (n : ℝ) ≤ 2 * m := by
    have : ((n : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hn.le
    push_cast at this
    exact this
  -- `log(n/m) ≥ (n − m)/(2m)`
  have hgap : ((n : ℝ) - m) / (2 * m) ≤ Real.log n - Real.log m := by
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn' hm')
    rw [Real.log_div hn'.ne' hm'.ne', inv_div] at h1
    have h2 : ((n : ℝ) - m) / (2 * m) ≤ ((n : ℝ) - m) / n :=
      div_le_div_of_nonneg_left hhpos.le hn' hnle
    have h3 : ((n : ℝ) - m) / n = 1 - m / n := by
      field_simp
    linarith
  have hgpos : 0 < Real.log n - Real.log m := lt_of_lt_of_le (by positivity) hgap
  have hx : H * (Real.log m - Real.log n) / 2 ≠ 0 := by
    have : Real.log m - Real.log n ≠ 0 := by
      intro h0
      linarith
    positivity
  refine (sinc_sq_le_inv_sq hx).trans ?_
  rw [hh]
  have hsq : (((n : ℝ) - m) / (2 * m)) ^ 2 ≤ (Real.log n - Real.log m) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hgap 2
  have e1 : (H * (Real.log m - Real.log n) / 2) ^ 2 = H ^ 2 * (Real.log n - Real.log m) ^ 2 / 4 := by ring
  rw [e1, one_div_div, div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_pow, div_le_iff₀ (by positivity)] at hsq
  have hHpos : 0 ≤ 4 * H ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hsq hHpos
  nlinarith

/-- The clock kernel on a far pair of integers. -/
theorem sinc_sq_far_le {m n : ℕ} (hm : 0 < m) (hn : 2 * m ≤ n) {H : ℝ} (hH : 0 < H) :
    Real.sinc (H * (Real.log m - Real.log n) / 2) ^ 2 ≤ 16 / H ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hnle : 2 * (m : ℝ) ≤ n := by
    have : ((2 * m : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at this
    exact this
  have hn' : (0 : ℝ) < n := by linarith
  have hgap : 1 / 2 ≤ Real.log n - Real.log m := by
    have h1 : Real.log 2 ≤ Real.log (n / m) :=
      Real.log_le_log (by norm_num) (by
        rw [le_div_iff₀ hm']
        exact hnle)
    rw [Real.log_div hn'.ne' hm'.ne'] at h1
    have := Real.log_two_gt_d9
    linarith
  have hx : H * (Real.log m - Real.log n) / 2 ≠ 0 := by
    have : Real.log m - Real.log n ≠ 0 := by
      intro h0
      linarith
    positivity
  refine (sinc_sq_le_inv_sq hx).trans ?_
  have e1 : (H * (Real.log m - Real.log n) / 2) ^ 2 = H ^ 2 * (Real.log n - Real.log m) ^ 2 / 4 := by ring
  rw [e1, one_div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : (1 / 2 : ℝ) ^ 2 ≤ (Real.log n - Real.log m) ^ 2 := pow_le_pow_left₀ (by norm_num) hgap 2
  have hHpos : 0 < H ^ 2 := by positivity
  nlinarith

section Critical

variable {Q : Finset ℕ} {k : ℕ}

/-- The weights `r^{−σ}`. -/
def powWeight (σ : ℝ) (r : ℕ) : ℝ := (r : ℝ) ^ (-σ)

theorem powWeight_nonneg (σ : ℝ) (r : ℕ) : 0 ≤ powWeight σ r := Real.rpow_nonneg (Nat.cast_nonneg r) _

/-- The sum of a power of the product over all tuples. -/
theorem sum_tupleProd_rpow (β : ℝ) :
    ∑ u : Fin k → Q, ((tupleProd u : ℕ) : ℝ) ^ β = (∑ r ∈ Q, (r : ℝ) ^ β) ^ k := by
  have h := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset Q))
    (fun _ r => ((r : ℕ) : ℝ) ^ β)
  rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have e : ∑ r : Q, ((r : ℕ) : ℝ) ^ β = ∑ r ∈ Q, (r : ℝ) ^ β := Finset.sum_coe_sort Q fun r => (r : ℝ) ^ β
  rw [e] at h
  rw [h]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold tupleProd
  push_cast
  exact (Real.finsetProd_rpow _ _ (fun s _ => Nat.cast_nonneg _) β).symm

/-- A tuple has the weight of its product. -/
theorem tupleWeight_eq [DecidableEq Q] (σ : ℝ) (ha : ∀ r ∈ Q, 0 ≤ powWeight σ r) (u : Fin k → Q) :
    (primeSystem Q (powWeight σ) ha).tupleWeight u = ((tupleProd u : ℕ) : ℝ) ^ (-σ) := by
  unfold PhaseSystem.tupleWeight primeSystem tupleProd powWeight
  push_cast
  exact Real.finsetProd_rpow _ _ (fun s _ => Nat.cast_nonneg _) (-σ)

open Classical in
/-- **The inner sum.** The tuples with a larger product, from a given tuple. -/
theorem sum_gt_le (hQ : ∀ r ∈ Q, r.Prime) {σ : ℝ} (hσ : 0 ≤ σ) (u : Fin k → Q) {H : ℝ} (hH : 0 < H) :
    ∑ v : Fin k → Q, (if tupleProd u < tupleProd v then
        ((tupleProd v : ℕ) : ℝ) ^ (-σ) *
          Real.sinc (H * (Real.log (tupleProd u) - Real.log (tupleProd v)) / 2) ^ 2 else 0) ≤
      k.factorial * ((tupleProd u : ℕ) : ℝ) ^ (-σ) * (12 * (tupleProd u : ℕ) / H) +
        16 / H ^ 2 * (∑ r ∈ Q, (r : ℝ) ^ (-σ)) ^ k := by
  set m := tupleProd u with hm
  have hmpos : 0 < m := tupleProd_pos hQ u
  have hm' : (0 : ℝ) < m := by exact_mod_cast hmpos
  set κ : ℕ → ℝ := fun n => Real.sinc (H * (Real.log m - Real.log n) / 2) ^ 2 with hκ
  have hκ0 : ∀ n, 0 ≤ κ n := fun n => sq_nonneg _
  have hvpos : ∀ v : Fin k → Q, (0 : ℝ) < ((tupleProd v : ℕ) : ℝ) := fun v => by
    exact_mod_cast tupleProd_pos hQ v
  have hrnn : ∀ v : Fin k → Q, 0 ≤ ((tupleProd v : ℕ) : ℝ) ^ (-σ) := fun v =>
    Real.rpow_nonneg (hvpos v).le _
  -- Split into near and far.
  have hsplit : ∀ v : Fin k → Q, (if m < tupleProd v then ((tupleProd v : ℕ) : ℝ) ^ (-σ) * κ (tupleProd v) else 0) ≤
      (m : ℝ) ^ (-σ) * (if m < tupleProd v ∧ tupleProd v < 2 * m then κ (tupleProd v) else 0) +
        16 / H ^ 2 * ((tupleProd v : ℕ) : ℝ) ^ (-σ) := by
    intro v
    have h16 : 0 ≤ 16 / H ^ 2 * ((tupleProd v : ℕ) : ℝ) ^ (-σ) := mul_nonneg (by positivity) (hrnn v)
    by_cases h1 : m < tupleProd v
    · rw [if_pos h1]
      by_cases h2 : tupleProd v < 2 * m
      · rw [if_pos ⟨h1, h2⟩]
        have hle : ((tupleProd v : ℕ) : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hm' (by exact_mod_cast h1.le) (by linarith)
        have := mul_le_mul_of_nonneg_right hle (hκ0 (tupleProd v))
        linarith
      · rw [if_neg (fun h => h2 h.2), mul_zero, zero_add, mul_comm]
        exact mul_le_mul_of_nonneg_right (sinc_sq_far_le hmpos (not_lt.mp h2) hH) (hrnn v)
    · rw [if_neg h1, if_neg (fun h => h1 h.1), mul_zero, zero_add]
      exact h16
  refine (Finset.sum_le_sum fun v _ => hsplit v).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_tupleProd_rpow (-σ)]
  refine add_le_add ?_ le_rfl
  -- The near part: at most `k!` tuples over each integer.
  set f : ℕ → ℝ := fun n => if m < n ∧ n < 2 * m then κ n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]
    split_ifs
    · exact hκ0 n
    · exact le_rfl
  have hcomp := Finset.sum_comp (s := (Finset.univ : Finset (Fin k → Q))) f tupleProd
  simp only [nsmul_eq_mul] at hcomp
  set A := (Finset.univ : Finset (Fin k → Q)).image tupleProd with hA
  have hfib : ∀ n ∈ A, (((Finset.univ.filter fun v : Fin k → Q => tupleProd v = n).card : ℕ) : ℝ) * f n ≤
      (k.factorial : ℝ) * f n := by
    intro n hn
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hn
    refine mul_le_mul_of_nonneg_right ?_ (hf0 _)
    exact_mod_cast card_fiber_le hQ v
  have hsum1 : ∑ v : Fin k → Q, f (tupleProd v) ≤ (k.factorial : ℝ) * ∑ n ∈ A, f n := by
    rw [hcomp, Finset.mul_sum]
    exact Finset.sum_le_sum hfib
  -- The integers in `(m, 2m)` have total kernel mass at most `3X`.
  set X : ℝ := 4 * (m : ℝ) / H with hX
  have hXpos : 0 < X := by positivity
  have hsum2 : ∑ n ∈ A, f n ≤ 3 * X := by
    have h1 : ∑ n ∈ A, f n ≤ ∑ n ∈ Finset.Ioo m (2 * m), min 1 (X ^ 2 / (((n - m : ℕ) : ℝ)) ^ 2) := by
      have hnn : ∀ n, 0 ≤ min 1 (X ^ 2 / (((n - m : ℕ) : ℝ)) ^ 2) := fun n =>
        le_min zero_le_one (by positivity)
      calc ∑ n ∈ A, f n ≤ ∑ n ∈ A.filter (fun n => m < n ∧ n < 2 * m), κ n := by
            rw [Finset.sum_filter]
        _ ≤ ∑ n ∈ A.filter (fun n => m < n ∧ n < 2 * m), min 1 (X ^ 2 / (((n - m : ℕ) : ℝ)) ^ 2) := by
            refine Finset.sum_le_sum fun n hn => ?_
            obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hn).2
            exact sinc_sq_near_le hmpos h1 h2 hH
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hnn n
            obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hn).2
            exact Finset.mem_Ioo.mpr ⟨h1, h2⟩
    refine h1.trans ?_
    have hinj : Set.InjOn (fun n : ℕ => n - m) (Finset.Ioo m (2 * m) : Set ℕ) := by
      intro a ha b hb he
      have h3 := (Finset.mem_Ioo.mp ha).1
      have h4 := (Finset.mem_Ioo.mp hb).1
      simp only at he
      omega
    have hs : ∑ n ∈ Finset.Ioo m (2 * m), min 1 (X ^ 2 / (((n - m : ℕ) : ℝ)) ^ 2) =
        ∑ h ∈ (Finset.Ioo m (2 * m)).image (fun n => n - m), min 1 (X ^ 2 / ((h : ℕ) : ℝ) ^ 2) := by
      rw [Finset.sum_image hinj]
    rw [hs]
    refine le_trans ?_ (sum_min_le hXpos m)
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) fun h _ _ =>
      le_min zero_le_one (by positivity)
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hk0 : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
  have hmσ : 0 ≤ (m : ℝ) ^ (-σ) := Real.rpow_nonneg hm'.le _
  have e : (k.factorial : ℝ) * (m : ℝ) ^ (-σ) * (12 * (m : ℝ) / H) =
      (m : ℝ) ^ (-σ) * ((k.factorial : ℝ) * (3 * X)) := by
    rw [hX]
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (hsum1.trans ?_) hmσ
  exact mul_le_mul_of_nonneg_left hsum2 hk0

open Classical in
/-- **The energy at every `k`.** See the module docstring. -/
theorem energy_le_past_diagonal (hQ : ∀ r ∈ Q, r.Prime) {σ : ℝ} (hσ : 0 ≤ σ)
    (ha : ∀ r ∈ Q, 0 ≤ powWeight σ r) (k : ℕ) {H : ℝ} (hH : 0 < H) :
    (primeSystem Q (powWeight σ) ha).energy k H ≤
      k.factorial * (∑ r ∈ Q, powWeight σ r ^ 2) ^ k +
        24 * k.factorial * (∑ r ∈ Q, (r : ℝ) ^ (1 - 2 * σ)) ^ k / H +
        32 * (∑ r ∈ Q, powWeight σ r) ^ (2 * k) / H ^ 2 := by
  set S := primeSystem Q (powWeight σ) ha with hS
  set n : (Fin k → Q) → ℕ := tupleProd with hn
  have hstep : ∀ u : Fin k → Q, S.tupleStep u = Real.log (n u) := primeSystem_tupleStep hQ _ ha
  have hW : ∀ u : Fin k → Q, S.tupleWeight u = ((n u : ℕ) : ℝ) ^ (-σ) := tupleWeight_eq σ ha
  have hnpos : ∀ u : Fin k → Q, (0 : ℝ) < ((n u : ℕ) : ℝ) := fun u => by
    exact_mod_cast tupleProd_pos hQ u
  set W : (Fin k → Q) → ℝ := fun u => ((n u : ℕ) : ℝ) ^ (-σ) with hWdef
  have hW0 : ∀ u, 0 ≤ W u := fun u => Real.rpow_nonneg (hnpos u).le _
  set κ : (Fin k → Q) → (Fin k → Q) → ℝ := fun u v =>
    Real.sinc (H * (Real.log (n u) - Real.log (n v)) / 2) ^ 2 with hκ
  have hκ0 : ∀ u v, 0 ≤ κ u v := fun u v => sq_nonneg _
  have hκsymm : ∀ u v, κ v u = κ u v := fun u v => by
    simp only [hκ]
    have e : H * (Real.log (n v) - Real.log (n u)) / 2 = -(H * (Real.log (n u) - Real.log (n v)) / 2) := by
      ring
    rw [e, Real.sinc_neg]
  have hE : S.energy k H = ∑ u, ∑ v, W u * W v * κ u v := by
    unfold PhaseSystem.energy
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hW, hW, hstep, hstep]
  -- The trichotomy.
  have htri : ∀ u v, W u * W v * κ u v =
      (if n u = n v then W u * W v * κ u v else 0) +
        (if n u < n v then W u * W v * κ u v else 0) +
        (if n v < n u then W v * W u * κ v u else 0) := by
    intro u v
    rcases lt_trichotomy (n u) (n v) with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp only [h.ne', not_lt.mpr h.le, h, if_true, if_false, zero_add, hκsymm u v]
      ring
  have hswap : ∑ u, ∑ v, (if n v < n u then W v * W u * κ v u else 0) =
      ∑ u, ∑ v, (if n u < n v then W u * W v * κ u v else 0) := Finset.sum_comm
  have hdecomp : S.energy k H = ∑ u, ∑ v, (if n u = n v then W u * W v * κ u v else 0) +
      2 * ∑ u, ∑ v, (if n u < n v then W u * W v * κ u v else 0) := by
    rw [hE]
    calc ∑ u, ∑ v, W u * W v * κ u v = ∑ u, ∑ v, ((if n u = n v then W u * W v * κ u v else 0) +
          (if n u < n v then W u * W v * κ u v else 0) +
          (if n v < n u then W v * W u * κ v u else 0)) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => htri u v
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [hswap]
          ring
  -- The diagonal.
  have hdiag : ∑ u, ∑ v, (if n u = n v then W u * W v * κ u v else 0) ≤
      k.factorial * (∑ r ∈ Q, powWeight σ r ^ 2) ^ k := by
    have hsq := sum_tupleWeight_sq (k := k) (powWeight σ) ha
    rw [← hsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    have hstepu : ∀ v, (if n u = n v then W u * W v * κ u v else 0) ≤
        if n v = n u then W u ^ 2 else 0 := by
      intro v
      by_cases h : n u = n v
      · rw [if_pos h, if_pos h.symm]
        have hWv : W v = W u := by
          simp only [hWdef]
          rw [h]
        rw [hWv]
        have hk1 : κ u v ≤ 1 := sinc_sq_le_one _
        have : 0 ≤ W u * W u := mul_nonneg (hW0 u) (hW0 u)
        nlinarith
      · rw [if_neg h, if_neg (Ne.symm h)]
    refine (Finset.sum_le_sum fun v _ => hstepu v).trans ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hW u]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact_mod_cast card_fiber_le hQ u
  -- The off-diagonal.
  have hoff : ∑ u, ∑ v, (if n u < n v then W u * W v * κ u v else 0) ≤
      12 * k.factorial * (∑ r ∈ Q, (r : ℝ) ^ (1 - 2 * σ)) ^ k / H +
        16 * (∑ r ∈ Q, powWeight σ r) ^ (2 * k) / H ^ 2 := by
    have hu : ∀ u, ∑ v, (if n u < n v then W u * W v * κ u v else 0) ≤
        12 * k.factorial / H * ((n u : ℕ) : ℝ) ^ (1 - 2 * σ) +
          16 / H ^ 2 * (∑ r ∈ Q, (r : ℝ) ^ (-σ)) ^ k * W u := by
      intro u
      have h1 := sum_gt_le hQ hσ u hH
      have e1 : ∑ v, (if n u < n v then W u * W v * κ u v else 0) =
          W u * ∑ v, (if n u < n v then W v * κ u v else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs
        · ring
        · simp
      rw [e1]
      have h2 := mul_le_mul_of_nonneg_left h1 (hW0 u)
      refine h2.trans (le_of_eq ?_)
      have hp := hnpos u
      have e2 : W u * ((n u : ℕ) : ℝ) ^ (-σ) * ((n u : ℕ) : ℝ) = ((n u : ℕ) : ℝ) ^ (1 - 2 * σ) := by
        have e3 : (1 : ℝ) - 2 * σ = -σ + -σ + 1 := by ring
        rw [e3, Real.rpow_add hp, Real.rpow_add hp, Real.rpow_one]
      simp only [hn] at e2 ⊢
      have e4 : W u * ((k.factorial : ℝ) * ((tupleProd u : ℕ) : ℝ) ^ (-σ) * (12 * ((tupleProd u : ℕ) : ℝ) / H) +
          16 / H ^ 2 * (∑ r ∈ Q, (r : ℝ) ^ (-σ)) ^ k) =
          12 * k.factorial / H * (W u * ((tupleProd u : ℕ) : ℝ) ^ (-σ) * ((tupleProd u : ℕ) : ℝ)) +
            16 / H ^ 2 * (∑ r ∈ Q, (r : ℝ) ^ (-σ)) ^ k * W u := by
        ring
      rw [e4, e2]
    refine (Finset.sum_le_sum fun u _ => hu u).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_tupleProd_rpow (1 - 2 * σ)]
    have hsumW : ∑ u, W u = (∑ r ∈ Q, (r : ℝ) ^ (-σ)) ^ k := sum_tupleProd_rpow (-σ)
    rw [hsumW]
    have e5 : ∑ r ∈ Q, powWeight σ r = ∑ r ∈ Q, (r : ℝ) ^ (-σ) := rfl
    rw [e5, pow_mul']
    ring
  rw [hdecomp]
  have e6 : 24 * (k.factorial : ℝ) * (∑ r ∈ Q, (r : ℝ) ^ (1 - 2 * σ)) ^ k / H =
      2 * (12 * k.factorial * (∑ r ∈ Q, (r : ℝ) ^ (1 - 2 * σ)) ^ k / H) := by ring
  have e7 : 32 * (∑ r ∈ Q, powWeight σ r) ^ (2 * k) / H ^ 2 =
      2 * (16 * (∑ r ∈ Q, powWeight σ r) ^ (2 * k) / H ^ 2) := by ring
  rw [e6, e7]
  linarith

open Classical in
/-- **Large values past the diagonal.** At every `k` and every `H`, with no relation between them. -/
theorem card_largeValue_le_past_diagonal (hQ : ∀ r ∈ Q, r.Prime) {σ : ℝ} (hσ : 0 ≤ σ)
    (ha : ∀ r ∈ Q, 0 ≤ powWeight σ r) {k : ℕ} (hk : 1 ≤ k) {Λ θ T₀ H : ℝ} (hΛ0 : 0 < Λ)
    (hΛ : ∀ r ∈ Q, Real.log r ≤ Λ) (hθ0 : 0 < θ) (hH0 : 0 < H)
    (R : Finset ℝ) (hmid : ∀ τ ∈ R, |τ - T₀| + θ / (4 * k * Λ) ≤ H / 2)
    (hR : ∀ τ ∈ R, τ ∈ (primeSystem Q (powWeight σ) ha).largeValue θ)
    (hsep : ∀ τ ∈ R, ∀ τ' ∈ R, τ ≠ τ' → 2 * (θ / (4 * k * Λ)) ≤ |τ - τ'|) :
    (R.card : ℝ) * (θ / (4 * k * Λ)) * (θ * ∑ r ∈ Q, powWeight σ r) ^ (2 * k) / (2 * H) ≤
      k.factorial * (∑ r ∈ Q, powWeight σ r ^ 2) ^ k +
        24 * k.factorial * (∑ r ∈ Q, (r : ℝ) ^ (1 - 2 * σ)) ^ k / H +
        32 * (∑ r ∈ Q, powWeight σ r) ^ (2 * k) / H ^ 2 := by
  set S := primeSystem Q (powWeight σ) ha with hS
  have hstep : ∀ i, |S.step i| ≤ Λ := by
    intro r
    have h0 : 0 ≤ Real.log ((r : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [show S.step r = Real.log ((r : ℕ) : ℝ) from rfl, abs_of_nonneg h0]
    exact hΛ _ r.2
  have h1 := PhaseSystem.card_mul_le_clockedMoment (S := S) hk hΛ0 hstep hθ0 hH0 R hmid hR hsep
  rw [PhaseSystem.clockedMoment_eq _ _ _ hH0, primeSystem_size] at h1
  have h2 := (le_abs_self _).trans (S.abs_shiftedEnergy_le_energy k T₀ H)
  exact h1.trans (h2.trans (energy_le_past_diagonal hQ hσ ha k hH0))

end Critical

/-! ### The oscillating energy -/

/-- The clock has mass `1`. -/
theorem integral_clock_one (T₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) = H := by
  have h := integral_clock_cos T₀ hH 0
  simpa using h

/-- **The oscillating energy is bounded by the modulus on the window.** -/
theorem shiftedEnergy_le_of_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (S : PhaseSystem ι) (k : ℕ)
    (T₀ : ℝ) {H s : ℝ} (hH : 0 < H) (hs : ∀ t ∈ Set.Icc (T₀ - H) (T₀ + H), ‖S.poly t‖ ≤ s) :
    S.shiftedEnergy k T₀ H ≤ s ^ (2 * k) := by
  rw [← S.clockedMoment_eq k T₀ hH]
  unfold PhaseSystem.clockedMoment
  have hcp := S.continuous_poly
  have hc1 : Continuous fun t : ℝ => (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k) := by fun_prop
  have hc2 : Continuous fun t : ℝ => (1 - |t - T₀| / H) * s ^ (2 * k) := by fun_prop
  have hint : ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k) ≤
      ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * s ^ (2 * k) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) fun t ht => ?_
    have h1 : 0 ≤ 1 - |t - T₀| / H := by
      rw [sub_nonneg, div_le_one hH, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hs t ht) _) h1
  rw [intervalIntegral.integral_mul_const, integral_clock_one T₀ hH] at hint
  have hH' : 0 < 1 / H := by positivity
  calc _ ≤ 1 / H * (H * s ^ (2 * k)) := mul_le_mul_of_nonneg_left hint hH'.le
    _ = s ^ (2 * k) := by
        field_simp

theorem powWeight_half (r : ℕ) : powWeight (1 / 2) r = 1 / √(r : ℝ) := by
  unfold powWeight
  rw [Real.rpow_neg (Nat.cast_nonneg r), ← Real.sqrt_eq_rpow, one_div]

/-- The polynomial of the critical system. -/
theorem poly_critical (Q : Finset ℕ) (ha : ∀ r ∈ Q, 0 ≤ powWeight (1 / 2) r) (t : ℝ) :
    (primeSystem Q (powWeight (1 / 2)) ha).poly t =
      ∑ p ∈ Q, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p)) := by
  unfold PhaseSystem.poly
  rw [← Finset.sum_coe_sort Q fun p => ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e1 : (primeSystem Q (powWeight (1 / 2)) ha).weight r = 1 / √((r : ℕ) : ℝ) := powWeight_half r
  have e2 : (primeSystem Q (powWeight (1 / 2)) ha).step r = Real.log ((r : ℕ) : ℝ) := rfl
  rw [e1, e2]
  congr 2
  push_cast
  ring

/-- **The oscillating energy stays below size.** With `L = log 2T`, `ℓ = log L`, for `N` past `10⁹ L⁶ ℓ⁴`, all `k`, and all `H ≤ T/2`, the clocked moment at height `T` of the critical column
is at most `(S − 1/(10²⁵ L¹⁹ ℓ¹⁴))^{2k}`. -/
theorem shiftedEnergy_critical_le :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ,
      10 ^ 9 * Real.log (2 * T) ^ 6 * Real.log (Real.log (2 * T)) ^ 4 < N →
      ∀ (ha : ∀ r ∈ N.primesBelow, 0 ≤ powWeight (1 / 2) r) (k : ℕ) (H : ℝ), 0 < H → H ≤ T / 2 →
      (primeSystem N.primesBelow (powWeight (1 / 2)) ha).shiftedEnergy k T H ≤
        ((∑ p ∈ N.primesBelow, powWeight (1 / 2) p) -
          1 / (10 ^ 25 * Real.log (2 * T) ^ 19 * Real.log (Real.log (2 * T)) ^ 14)) ^ (2 * k) := by
  obtain ⟨T₁, hT₁, hnorm⟩ := norm_sum_primes_le
  obtain ⟨T₂, hT₂, hsize⟩ := eventually_heightSize
  refine ⟨2 * max T₁ T₂, by positivity, fun T hT N hN ha k H hH hHT => ?_⟩
  have hmax : 0 < max T₁ T₂ := lt_of_lt_of_le hT₁ (le_max_left _ _)
  have hTpos : 0 < T := by linarith
  refine shiftedEnergy_le_of_norm_le _ k T hH fun t ht => ?_
  have ht1 : T / 2 ≤ t := by linarith [ht.1]
  have ht2 : t ≤ 2 * T := by linarith [ht.2]
  have htabs : |t| = t := abs_of_nonneg (by linarith)
  have hge : max T₁ T₂ ≤ |t| := by
    rw [htabs]
    linarith
  have h := hsize t ((le_max_right _ _).trans hge)
  rw [poly_critical]
  have hb := hnorm t ((le_max_left _ _).trans hge) N
  rw [htabs] at hb h
  have hL0 : Real.log t ≤ Real.log (2 * T) := Real.log_le_log (by linarith) ht2
  generalize Real.log t = Lt at h hb hL0
  generalize Real.log (2 * T) = L at hL0 hN ⊢
  have hLt100 := h.hundred_le
  have hℓt := h.one_le
  have hℓle : Real.log Lt ≤ Real.log L := Real.log_le_log (by linarith) hL0
  generalize Real.log Lt = ℓt at h hb hℓle hℓt
  generalize Real.log L = ℓ at hℓle hN ⊢
  have hsum : ∑ p ∈ N.primesBelow, powWeight (1 / 2) p = ∑ p ∈ N.primesBelow, 1 / √(p : ℝ) :=
    Finset.sum_congr rfl fun p _ => powWeight_half p
  rw [hsum]
  have hLtpos : 0 < Lt := by linarith
  have hℓtpos : 0 < ℓt := by linarith
  have hLpos : 0 < L := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hmono : 10 ^ 9 * Lt ^ 6 * ℓt ^ 4 < N := lt_of_le_of_lt (by gcongr) hN
  have hb' := hb hmono
  have hinv : 1 / (10 ^ 25 * L ^ 19 * ℓ ^ 14) ≤ 1 / (10 ^ 25 * Lt ^ 19 * ℓt ^ 14) :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
