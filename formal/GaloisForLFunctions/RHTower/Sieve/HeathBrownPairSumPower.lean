import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumMajorant
import GaloisForLFunctions.RHTower.Sieve.PowerFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOne

/-!
# Heath-Brown's pair sums: powers, the divisor bound and Hölder

For a polynomial `D(t) = Σ_{n∈S} a_n n^{it}` with `S ⊆ (A, B]` and `|a_n| ≤ n^{−σ}`, the `k`-th
power is the polynomial of the `k`-fold Dirichlet convolution (corpus `dirPoly_convPow`).  Its
coefficient at `u` is a sum over the ordered `k`-factorisations of `u` with factors in `S`; each
term has modulus at most `u^{−σ}`, the number of terms is at most `d(u)^k`
(`powFibreOn_univ_card_le_divisors`), and the coefficient vanishes unless `u ∈ (A^k, B^k]`.  The
majorant principle therefore gives the `2k`-th moment over pairs of points of `W`

`Σ_{t₁,t₂∈W} |D(t₁ − t₂)|^{2k} ≤ D^{2k} Σ_{t₁,t₂∈W} |Σ_{A^k<u≤B^k} u^{−σ+i(t₁−t₂)}|²`

whenever `d(u) ≤ D` on `(A^k, B^k]`.  With Hölder over the `|W|²` pairs this is Guth–Maynard (6.2)
and, for `k = 2`, the Cauchy–Schwarz step of Heath-Brown's Corollary 2.1:

`(Σ_{t₁,t₂∈W} |D(t₁−t₂)|²)² ≤ |W|² D⁴ Σ_{t₁,t₂∈W} |Σ_{A²<u≤B²} u^{−σ+i(t₁−t₂)}|²`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The zero-extended coefficient vector of `a` on `S`, indexed by `Fin B` (`i ↔ n = i+1`). -/
def hbFinCoeff (B : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) : Fin B → ℂ :=
  fun i => if (i : ℕ) + 1 ∈ S then a ((i : ℕ) + 1) else 0

/-- The coefficient at `u` of the `k`-th power of the polynomial on `S ⊆ [1, B]`. -/
def hbPowCoeff (B k : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (u : ℕ) : ℂ :=
  if h : u - 1 < B ^ k then convPow B k (hbFinCoeff B S a) ⟨u - 1, h⟩ else 0

/-- **The `k`-th power is a Dirichlet polynomial** on `[1, B^k]`. -/
theorem hbPoly_pow {S : Finset ℕ} {B : ℕ} (hS : S ⊆ Finset.Icc 1 B) (a : ℕ → ℂ) (k : ℕ)
    (t : ℝ) : hbPoly S a t ^ k = hbPoly (Finset.Icc 1 (B ^ k)) (hbPowCoeff B k S a) t := by
  rw [hbPoly_eq_dirPoly hS, ← dirPoly_convPow, dirPoly_eq_hbPoly]
  rfl

/-- A factorisation with all factors in `S ⊆ (A, B]` has product in `(A^k, B^k]`. -/
private theorem powIdx_succ_mem_Ioc {A B k : ℕ} (hk : 1 ≤ k) {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioc A B) (p : Fin k → Fin B) (hall : ∀ i, (p i : ℕ) + 1 ∈ S) :
    (powIdx p : ℕ) + 1 ∈ Finset.Ioc (A ^ k) (B ^ k) := by
  have hmem : ∀ i, A < (p i : ℕ) + 1 ∧ (p i : ℕ) + 1 ≤ B := fun i =>
    Finset.mem_Ioc.mp (hS (hall i))
  rw [powIdx_val_add_one, Finset.mem_Ioc]
  constructor
  · calc A ^ k < (A + 1) ^ k := Nat.pow_lt_pow_left (Nat.lt_succ_self A) (by omega)
      _ = ∏ _i : Fin k, (A + 1) := by simp
      _ ≤ ∏ i : Fin k, ((p i : ℕ) + 1) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => (hmem i).1
  · calc ∏ i : Fin k, ((p i : ℕ) + 1) ≤ ∏ _i : Fin k, B :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => (hmem i).2
      _ = B ^ k := by simp

/-- A term of the convolution with all factors in `S` has modulus at most `u^{−σ}`. -/
private theorem norm_prod_hbFinCoeff_le {B k : ℕ} {S : Finset ℕ} {σ : ℝ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ S, ‖a n‖ ≤ (n : ℝ) ^ (-σ)) (p : Fin k → Fin B)
    (hall : ∀ i, (p i : ℕ) + 1 ∈ S) :
    ‖∏ i, hbFinCoeff B S a (p i)‖ ≤ (((powIdx p : ℕ) + 1 : ℕ) : ℝ) ^ (-σ) := by
  rw [norm_prod, powIdx_val_add_one, Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ fun i _ => Nat.cast_nonneg _]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [hbFinCoeff, if_pos (hall i)]
  exact ha _ (hall i)

/-- A term with a factor outside `S` vanishes. -/
private theorem prod_hbFinCoeff_eq_zero {B k : ℕ} {S : Finset ℕ} (a : ℕ → ℂ)
    (p : Fin k → Fin B) (hnot : ¬ ∀ i, (p i : ℕ) + 1 ∈ S) :
    ∏ i, hbFinCoeff B S a (p i) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hbFinCoeff, if_neg hi])

/-- **Coefficients of the `k`-th power.**  For `u ≥ 1` the coefficient at `u` vanishes off
`(A^k, B^k]` and is at most `D^k u^{−σ}` there, when `|a_n| ≤ n^{−σ}` on `S ⊆ (A,B]` and
`d(u) ≤ D` on `(A^k, B^k]`. -/
theorem norm_hbPowCoeff_le {A B k : ℕ} (hk : 1 ≤ k) {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioc A B) {σ : ℝ} {a : ℕ → ℂ} (ha : ∀ n ∈ S, ‖a n‖ ≤ (n : ℝ) ^ (-σ))
    {D : ℝ} (hD : ∀ u ∈ Finset.Ioc (A ^ k) (B ^ k), (u.divisors.card : ℝ) ≤ D) {u : ℕ}
    (hu1 : 1 ≤ u) :
    ‖hbPowCoeff B k S a u‖ ≤
      if u ∈ Finset.Ioc (A ^ k) (B ^ k) then D ^ k * (u : ℝ) ^ (-σ) else 0 := by
  classical
  unfold hbPowCoeff
  by_cases h : u - 1 < B ^ k
  swap
  · have hu : u ∉ Finset.Ioc (A ^ k) (B ^ k) := fun hu => h (by
      have := Finset.mem_Ioc.mp hu; omega)
    rw [dif_neg h, if_neg hu, norm_zero]
  rw [dif_pos h]
  obtain ⟨j, hj⟩ : ∃ j : Fin (B ^ k), j = ⟨u - 1, h⟩ := ⟨_, rfl⟩
  rw [← hj]
  have hju : ∀ p ∈ (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j),
      (powIdx p : ℕ) + 1 = u := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2, hj]
    simp only
    omega
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j),
      ‖∏ i, hbFinCoeff B S a (p i)‖ ≤
        if u ∈ Finset.Ioc (A ^ k) (B ^ k) then (u : ℝ) ^ (-σ) else 0 := by
    intro p hp
    by_cases hall : ∀ i, (p i : ℕ) + 1 ∈ S
    · have hmem := powIdx_succ_mem_Ioc hk hS p hall
      rw [hju p hp] at hmem
      rw [if_pos hmem]
      have hle := norm_prod_hbFinCoeff_le ha p hall
      rwa [hju p hp] at hle
    · rw [prod_hbFinCoeff_eq_zero a p hall, norm_zero]
      split_ifs
      · positivity
      · exact le_refl 0
  by_cases hu : u ∈ Finset.Ioc (A ^ k) (B ^ k)
  · rw [if_pos hu]
    have hcard : (((Finset.univ : Finset (Fin k → Fin B)).filter
        (fun p => powIdx p = j)).card : ℝ) ≤ D ^ k := by
      have hfil : (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j) =
          powFibreOn B k Finset.univ j := by
        rw [powFibreOn]
        exact (Finset.filter_true_of_mem fun p _ i => Finset.mem_univ (p i)).symm
      have hle := powFibreOn_univ_card_le_divisors B k j
      have hj1 : (j : ℕ) + 1 = u := by
        rw [hj]
        simp only
        omega
      rw [hj1] at hle
      rw [hfil]
      calc ((powFibreOn B k Finset.univ j).card : ℝ) ≤ ((u.divisors.card : ℝ)) ^ k := by
            exact_mod_cast hle
        _ ≤ D ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) (hD u hu) k
    calc ‖convPow B k (hbFinCoeff B S a) j‖
        ≤ ∑ p ∈ (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j),
            ‖∏ i, hbFinCoeff B S a (p i)‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j),
            (u : ℝ) ^ (-σ) :=
          Finset.sum_le_sum fun p hp => le_of_le_of_eq (hterm p hp) (if_pos hu)
      _ = (((Finset.univ : Finset (Fin k → Fin B)).filter
            (fun p => powIdx p = j)).card : ℝ) * (u : ℝ) ^ (-σ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D ^ k * (u : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [if_neg hu]
    calc ‖convPow B k (hbFinCoeff B S a) j‖
        ≤ ∑ p ∈ (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j),
            ‖∏ i, hbFinCoeff B S a (p i)‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (Fin k → Fin B)).filter (fun p => powIdx p = j),
            (0 : ℝ) := Finset.sum_le_sum fun p hp => le_of_le_of_eq (hterm p hp) (if_neg hu)
      _ = 0 := by simp

/-- **The `2k`-th moment over pairs.**  If `|a_n| ≤ n^{−σ}` on `S ⊆ (A, B]` and `d(u) ≤ D` on
`(A^k, B^k]`, then
`Σ_{t₁,t₂} |D(t₁−t₂)|^{2k} ≤ D^{2k} Σ_{t₁,t₂} |Σ_{A^k<u≤B^k} u^{−σ+i(t₁−t₂)}|²`. -/
theorem sum_norm_hbPoly_pow_le (W : Finset ℝ) {A B k : ℕ} (hk : 1 ≤ k)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A B) {σ : ℝ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ S, ‖a n‖ ≤ (n : ℝ) ^ (-σ)) {D : ℝ}
    (hD : ∀ u ∈ Finset.Ioc (A ^ k) (B ^ k), (u.divisors.card : ℝ) ≤ D) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ (2 * k) ≤
      D ^ (2 * k) *
        hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun u => (((u : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
  classical
  have hSI : S ⊆ Finset.Icc 1 B := fun n hn => by
    have := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hII : Finset.Ioc (A ^ k) (B ^ k) ⊆ Finset.Icc 1 (B ^ k) := fun u hu => by
    have := Finset.mem_Ioc.mp hu
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hpow : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ (2 * k) =
      hbPairSum W (Finset.Icc 1 (B ^ k)) (hbPowCoeff B k S a) := by
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [← hbPoly_pow hSI, norm_pow, ← pow_mul, mul_comm]
  set b : ℕ → ℝ := fun u =>
    if u ∈ Finset.Ioc (A ^ k) (B ^ k) then D ^ k * (u : ℝ) ^ (-σ) else 0 with hb
  have hmaj := hbPairSum_le_of_norm_le W (S := Finset.Icc 1 (B ^ k))
    (a := hbPowCoeff B k S a) (b := b) fun u hu =>
      norm_hbPowCoeff_le hk hS ha hD (Finset.mem_Icc.mp hu).1
  have hres : hbPairSum W (Finset.Icc 1 (B ^ k)) (fun u => (b u : ℂ)) =
      hbPairSum W (Finset.Ioc (A ^ k) (B ^ k))
        (fun u => ((D ^ k : ℝ) : ℂ) * (((u : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
    have hfun : (fun u => (b u : ℂ)) = fun n => if n ∈ Finset.Ioc (A ^ k) (B ^ k) then
        ((D ^ k : ℝ) : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0 := by
      funext u
      simp only [hb]
      split_ifs <;> push_cast <;> ring
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [hbPoly_eq_ite_of_subset hII, hfun]
  rw [hpow]
  refine hmaj.trans (le_of_eq ?_)
  rw [hres, hbPairSum_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← pow_mul,
    mul_comm k 2]

/-- **Hölder over the pairs** (Guth–Maynard (6.2)):
`Σ_{t₁,t₂} x ≤ (|W|²)^{1−1/k} (Σ_{t₁,t₂} x^k)^{1/k}` for `x = |D(t₁−t₂)|²`. -/
theorem hbPairSum_le_card_rpow_mul_moment (W : Finset ℝ) {k : ℕ}
    (hk : 1 ≤ k) (S : Finset ℕ) (a : ℕ → ℂ) :
    hbPairSum W S a ≤ ((W.card : ℝ) ^ 2) ^ (1 - 1 / (k : ℝ)) *
      (∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ (2 * k)) ^ (1 / (k : ℝ)) := by
  have h := RHTower.GuthMaynard.sum_le_card_rpow_mul_sum_pow_rpow (W ×ˢ W)
    (fun p => ‖hbPoly S a (p.1 - p.2)‖ ^ 2) (fun _ _ => by positivity) hk
  have hcard : ((W ×ˢ W).card : ℝ) = (W.card : ℝ) ^ 2 := by
    rw [Finset.card_product]
    push_cast
    ring
  simp only [← pow_mul] at h
  rw [hcard, Finset.sum_product, Finset.sum_product] at h
  exact h

/-- **Guth–Maynard (6.2) with divisor-bounded coefficients.**  For `|a_n| ≤ n^{−σ}` on
`S ⊆ (A, B]` and `d ≤ D` on `(A^k, B^k]`:
`Σ_{t₁,t₂}|D(t₁−t₂)|² ≤ (|W|²)^{1−1/k} (D^{2k} Σ_{t₁,t₂}|Σ_{A^k<u≤B^k} u^{−σ+i(t₁−t₂)}|²)^{1/k}`. -/
theorem hbPairSum_le_power_lift (W : Finset ℝ) {A B k : ℕ}
    (hk : 1 ≤ k) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A B) {σ : ℝ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ S, ‖a n‖ ≤ (n : ℝ) ^ (-σ)) {D : ℝ}
    (hD : ∀ u ∈ Finset.Ioc (A ^ k) (B ^ k), (u.divisors.card : ℝ) ≤ D) :
    hbPairSum W S a ≤ ((W.card : ℝ) ^ 2) ^ (1 - 1 / (k : ℝ)) *
      (D ^ (2 * k) * hbPairSum W (Finset.Ioc (A ^ k) (B ^ k))
        (fun u => (((u : ℝ) ^ (-σ) : ℝ) : ℂ))) ^ (1 / (k : ℝ)) := by
  refine (hbPairSum_le_card_rpow_mul_moment W hk S a).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (sum_norm_hbPoly_pow_le W hk hS ha hD)
    (by positivity)

/-- **The fourth-moment step of Heath-Brown's Corollary 2.1** (squared form):
`(Σ_{t₁,t₂}|D(t₁−t₂)|²)² ≤ |W|² D⁴ Σ_{t₁,t₂}|Σ_{A²<u≤B²} u^{−σ+i(t₁−t₂)}|²`. -/
theorem hbPairSum_sq_le_fourthMoment (W : Finset ℝ) {A B : ℕ}
    {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A B) {σ : ℝ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ S, ‖a n‖ ≤ (n : ℝ) ^ (-σ)) {D : ℝ}
    (hD : ∀ u ∈ Finset.Ioc (A ^ 2) (B ^ 2), (u.divisors.card : ℝ) ≤ D) :
    hbPairSum W S a ^ 2 ≤ (W.card : ℝ) ^ 2 * D ^ 4 *
      hbPairSum W (Finset.Ioc (A ^ 2) (B ^ 2)) (fun u => (((u : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := W ×ˢ W)
    (f := fun p => ‖hbPoly S a (p.1 - p.2)‖ ^ 2)
  have hcard : ((W ×ˢ W).card : ℝ) = (W.card : ℝ) ^ 2 := by
    rw [Finset.card_product]
    push_cast
    ring
  rw [hcard, Finset.sum_product, Finset.sum_product] at hcs
  simp only [← pow_mul] at hcs
  have hmom := sum_norm_hbPoly_pow_le W (by norm_num) hS ha hD
  calc hbPairSum W S a ^ 2 ≤ (W.card : ℝ) ^ 2 *
        ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ (2 * 2) := hcs
    _ ≤ (W.card : ℝ) ^ 2 * (D ^ (2 * 2) *
        hbPairSum W (Finset.Ioc (A ^ 2) (B ^ 2)) (fun u => (((u : ℝ) ^ (-σ) : ℝ) : ℂ))) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)
    _ = _ := by ring

end

end RHTower.Sieve
