import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleLawOfEveryOrder

/-!
# Smooth large-scale rows of every order

Fix `L ≥ 0`, so that the cross-scale law has order `K = L + 1`. For a large-scale row `c'` put

`𝒮_L(c') = Σ_{t ≤ L} Σ_n |Δᵗ c'(n)|/n^{L+2-t}`,

a norm of `L`-fold smoothness (`Δ` the backward difference). For rows `c` on primes and `c'` supported
in `[L+1, N]`,

`|B(c, c') + m(c) R(c') + β(c) H(c')|
  ≤ C_L Σ_p |c(p)| (p^{L+1} 𝒮_L(c') + p⁻¹ Σ_n |c'(n)|/n²)`,  `C_L = 2(L+1) 4^L (L+1)!`.

**Mechanism.** The law of order `L + 1` leaves the potential terms `Σ_j Y_{p,i}(jn) u_i(jn)`, `i < L`.
* When `p ∤ j`, `n ↦ Y_{p,i}(jn)` is a `p`-periodic kernel with zero period sum. Then `L - i` periodic
  summations by parts in `n` cost `(2p)^{L+1} p/2` against `Σ_n |Δ^{L-i}(c'(n) u_i(jn))|`.
* The Leibniz bound and the step-`j` bound `|Δʳ u_i(j·)| ≤ jʳ u_{i+r}(j·)` turn this into
  `2^{L-i} (L+1)! j^{-(i+2)} 𝒮_L(c')`, which is summable in `j`.
* When `p | j`, the kernel is the constant `Y_{p,i}(0)`. These multiples contribute only
  `O(Σ_n |c'(n)|/n²)`, the equidistributed baseline.

**Exponent.** For `c'(n) = n² x(n)` with `x ≍ 1` smooth at scale `A` on `[A, 2A]`, one has
`𝒮_L ≍ A^{1-L}` and `Σ_n |c'(n)|/n² ≍ A`. For `c = 1` on the primes in `(P, 2P]` the bound is
`≍ P^{L+2} A^{1-L}/log P + A/log P`, against the diagonal `√(D(a) D(b)) ≍ A²/√(log P)`. That is
diagonal quality for `A ≥ P^{(L+2)/(L+1)}`, i.e. exponent `θ` up to `2(L+1)/(L+2) = 2K/(K+1)`:
`4/3, 3/2, 8/5, …` for `K = 2, 3, 4, …`, tending to `2`. Sharp cutoffs are not smooth beyond `K = 2`
and stop at `4/3`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The smoothness norm `𝒮_L(c') = Σ_{t ≤ L} Σ_{n ≤ N} |Δᵗ c'(n)|/n^{L+2-t}`. -/
def smoothnessNorm (N L : ℕ) (c' : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range (L + 1), ∑ n ∈ Icc 1 N, |bdiff^[t] c' n| / (n : ℝ) ^ (L + 2 - t)

/-! ## §1. Kernels `n ↦ Y(Jn)` -/

/-- Multiplication by a unit permutes residues: `Σ_{r < p} f(Jr) = Σ_{r < p} f(r)` for `p`-periodic `f`. -/
theorem sum_range_comp_mul_of_coprime {p J : ℕ} (hp : 0 < p) (hJ : Nat.Coprime p J)
    {f : ℕ → ℝ} (hf : Function.Periodic f p) :
    ∑ r ∈ range p, f (J * r) = ∑ r ∈ range p, f r := by
  classical
  have hinj : Set.InjOn (fun r => J * r % p) (range p : Set ℕ) := by
    intro a ha b hb h
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    have hmod : J * a ≡ J * b [MOD p] := h
    have := Nat.ModEq.cancel_left_of_coprime hJ hmod
    rw [Nat.ModEq, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    exact this
  have himg : (range p).image (fun r => J * r % p) = range p := by
    refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨r, -, rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (Nat.mod_lt _ hp)
    · rw [card_image_of_injOn hinj]
  calc ∑ r ∈ range p, f (J * r) = ∑ r ∈ range p, f (J * r % p) :=
        sum_congr rfl fun r _ => (hf.map_mod_nat _).symm
    _ = ∑ x ∈ (range p).image (fun r => J * r % p), f x := (sum_image hinj).symm
    _ = ∑ r ∈ range p, f r := by rw [himg]

theorem chainPotential_mul_periodic {p : ℕ} (hp : 0 < p) (i J : ℕ) :
    Function.Periodic (fun n => chainPotential p i (J * n)) p := fun n => by
  have hper : Function.Periodic (chainPotential p i) p := chainPotential_periodic hp i
  show chainPotential p i (J * (n + p)) = chainPotential p i (J * n)
  rw [mul_add]
  exact_mod_cast hper.nat_mul J (J * n)

/-! ## §2. One pair of indices `(i, j)` -/

/-- `J^r u_{i+r}(J(m+1)) ≤ (i+r+1)!/(J^{i+2} (m+1)^{i+r+2})`. -/
theorem pow_mul_pronicWeight_le {J : ℕ} (hJ : 1 ≤ J) (i r m : ℕ) :
    (J : ℝ) ^ r * pronicWeight (i + r) (J * (m + 1)) ≤
      ((i + r + 1).factorial : ℝ) / ((J : ℝ) ^ (i + 2) * ((m : ℝ) + 1) ^ (i + r + 2)) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h := pronicWeight_le (k := i + r) (M := J * (m + 1)) (by nlinarith)
  push_cast at h
  calc (J : ℝ) ^ r * pronicWeight (i + r) (J * (m + 1))
      ≤ (J : ℝ) ^ r * (((i + r + 1).factorial : ℝ) / ((J : ℝ) * ((m : ℝ) + 1)) ^ (i + r + 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((i + r + 1).factorial : ℝ) / ((J : ℝ) ^ (i + 2) * ((m : ℝ) + 1) ^ (i + r + 2)) := by
        rw [mul_pow, show i + r + 2 = r + (i + 2) by ring, pow_add (J : ℝ) r (i + 2)]
        field_simp

/-- The difference norm of one weight: for `J ≥ 1` and `S ≤ L - i`,
`Σ_{n ≤ N} |Δ^S (c'(n) u_i(Jn))| ≤ 2^S (L+1)!/J^{i+2} · 𝒮_L(c')` when `c'` vanishes on `[0, S]`. -/
theorem sum_abs_bdiff_iter_weight_le {N L i S J : ℕ} (hJ : 1 ≤ J) (hS : i + S = L)
    {c' : ℕ → ℝ} (hc0 : ∀ n ≤ S, c' n = 0) :
    ∑ n ∈ range (N + 1), |bdiff^[S] (fun n => c' n * pronicWeight i (J * n)) n| ≤
      2 ^ S * ((L + 1).factorial : ℝ) / (J : ℝ) ^ (i + 2) * smoothnessNorm N L c' := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  set x : ℕ → ℝ := fun n => c' n * pronicWeight i (J * n)
  have hx0 : bdiff^[S] x 0 = 0 :=
    bdiff_iter_apply_zero_of_vanish S x fun n hn => by simp only [x, hc0 n hn, zero_mul]
  rw [Finset.sum_range_succ', hx0, abs_zero, add_zero]
  -- shift to `n = m + 1`
  have hshift : ∀ m, bdiff^[S] x (m + 1) =
      bdiff^[S] (fun m => c' (m + 1) * pronicWeight i (J * (m + 1) + 0)) m := fun m => by
    have := bdiff_iter_shift S 1 x
    rw [show (fun n => x (n + 1)) = fun m => c' (m + 1) * pronicWeight i (J * (m + 1) + 0) from
      funext fun m => by simp only [x, add_zero]] at this
    rw [this]
  -- the Leibniz bound with the step-`J` majorants
  set μ : ℕ → ℕ → ℝ := fun r m => (J : ℝ) ^ r * pronicWeight (i + r) (J * (m + 1) + 0)
  have hμ : ∀ r m, |bdiff^[r] (fun m => pronicWeight i (J * (m + 1) + 0)) m| ≤ μ r m :=
    fun r m => abs_bdiff_iter_pronicWeight_le hJ r i 0 m
  have hμa : ∀ r, Antitone (μ r) := fun r a b hab => by
    simp only [μ, add_zero]
    exact mul_le_mul_of_nonneg_left (pronicWeight_anti (by nlinarith) (by nlinarith)) (by positivity)
  have hpt : ∀ m, |bdiff^[S] x (m + 1)| ≤ 2 ^ S * ((L + 1).factorial : ℝ) / (J : ℝ) ^ (i + 2) *
      ∑ t ∈ range (S + 1), |bdiff^[t] c' (m + 1)| / ((m : ℝ) + 1) ^ (L + 2 - t) := by
    intro m
    rw [hshift]
    refine (abs_bdiff_iter_mul_le S (fun m => c' (m + 1)) _ μ hμ hμa m).trans ?_
    rw [show 2 ^ S * ((L + 1).factorial : ℝ) / (J : ℝ) ^ (i + 2) *
        ∑ t ∈ range (S + 1), |bdiff^[t] c' (m + 1)| / ((m : ℝ) + 1) ^ (L + 2 - t) =
        2 ^ S * ∑ t ∈ range (S + 1), |bdiff^[t] c' (m + 1)| *
          (((L + 1).factorial : ℝ) / ((J : ℝ) ^ (i + 2) * ((m : ℝ) + 1) ^ (L + 2 - t))) by
      rw [mul_div_assoc, mul_assoc, mul_sum]
      congr 1
      refine sum_congr rfl fun t _ => ?_
      field_simp]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun t ht => ?_) (by positivity)
    have ht' := mem_range.mp ht
    rw [bdiff_iter_shift t 1 c']
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simp only [μ, add_zero]
    refine (pow_mul_pronicWeight_le hJ i (S - t) m).trans ?_
    rw [show i + (S - t) + 2 = L + 2 - t by omega]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.factorial_le (by omega : i + (S - t) + 1 ≤ L + 1)) (by positivity)
  calc ∑ m ∈ range N, |bdiff^[S] x (m + 1)|
      ≤ ∑ m ∈ range N, 2 ^ S * ((L + 1).factorial : ℝ) / (J : ℝ) ^ (i + 2) *
          ∑ t ∈ range (S + 1), |bdiff^[t] c' (m + 1)| / ((m : ℝ) + 1) ^ (L + 2 - t) :=
        sum_le_sum fun m _ => hpt m
    _ = 2 ^ S * ((L + 1).factorial : ℝ) / (J : ℝ) ^ (i + 2) *
          ∑ t ∈ range (S + 1), ∑ n ∈ Icc 1 N, |bdiff^[t] c' n| / (n : ℝ) ^ (L + 2 - t) := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun t _ => ?_
        rw [show Icc 1 N = Ico 1 (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
          sum_Ico_eq_sum_range, show N + 1 - 1 = N by omega]
        exact sum_congr rfl fun m _ => by rw [add_comm 1 m]; push_cast; ring
    _ ≤ 2 ^ S * ((L + 1).factorial : ℝ) / (J : ℝ) ^ (i + 2) * smoothnessNorm N L c' := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg
          (fun t ht => by simp only [mem_range] at ht ⊢; omega)
          fun t _ _ => sum_nonneg fun n _ => by positivity

/-! ## §3. The potential terms of one prime -/

theorem sum_ite_dvd_inv_pow_le {p q : ℕ} (hp : 0 < p) :
    ∑' j : ℕ, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (q + 2) else 0) ≤ 2 / (p : ℝ) ^ (q + 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hbase := hasSum_ite_dvd_inv_sq hp
  have hle : ∀ j : ℕ, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (q + 2) else 0) ≤
      1 / (p : ℝ) ^ q * (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) := fun j => by
    split_ifs with h
    · have hpj : (p : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.le_of_dvd (Nat.succ_pos j) h
      rw [div_mul_div_comm, one_mul, pow_add]
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpR.le hpj q) (by positivity)
    · simp
  have hs : Summable fun j : ℕ => (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (q + 2) else 0) :=
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) hle
      (hbase.summable.mul_left _)
  have h1 := Summable.tsum_le_tsum hle hs (hbase.summable.mul_left _)
  rw [tsum_mul_left, hbase.tsum_eq] at h1
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc ∑' j : ℕ, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (q + 2) else 0)
      ≤ 1 / (p : ℝ) ^ q * (Real.pi ^ 2 / 6 / (p : ℝ) ^ 2) := h1
    _ ≤ 1 / (p : ℝ) ^ q * (2 / (p : ℝ) ^ 2) := by gcongr
    _ = 2 / (p : ℝ) ^ (q + 2) := by rw [pow_add]; field_simp

/-- **One prime.** For `c'` supported in `[L+1, N]`:
`|Σ_n c'(n) Σ_{i<L} Σ_j Y_{p,i}(jn) u_i(jn)| ≤ L (2·4^L (L+1)! p^{L+2} 𝒮_L + 2^L L! Σ_n |c'(n)|/n²)`. -/
theorem abs_sum_mul_potentialTerms_le {p N L : ℕ} (hp : p.Prime) {c' : ℕ → ℝ}
    (hc' : ∀ n, c' n ≠ 0 → L + 1 ≤ n ∧ n ≤ N) :
    |∑ n ∈ Icc 1 N, c' n * potentialTerms p n L| ≤
      L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' +
        2 ^ L * (L.factorial : ℝ) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hzero : ∀ n, (n ≤ L ∨ N < n) → c' n = 0 := fun n hn => by
    by_contra h; have := hc' n h; omega
  have hSn : 0 ≤ smoothnessNorm N L c' :=
    sum_nonneg fun t _ => sum_nonneg fun n _ => by positivity
  have hM2 : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := sum_nonneg fun n _ => by positivity
  -- exchange the finite `n`-sum with the `j`-series
  set a : ℕ → ℕ → ℝ := fun i j => ∑ n ∈ Icc 1 N,
    c' n * (chainPotential p i ((j + 1) * n) * pronicWeight i ((j + 1) * n))
  have hsa : ∀ i, Summable (a i) := fun i =>
    summable_sum fun n hn => (summable_chainPotential_mul_pronicWeight hp0 (mem_Icc.mp hn).1 i).mul_left _
  have hre : ∑ n ∈ Icc 1 N, c' n * potentialTerms p n L = ∑ i ∈ range L, ∑' j, a i j := by
    simp only [potentialTerms, mul_sum, a]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun n hn =>
      (summable_chainPotential_mul_pronicWeight hp0 (mem_Icc.mp hn).1 i).mul_left _]
    exact sum_congr rfl fun n _ => (tsum_mul_left).symm
  rw [hre]
  -- bound each term `a i j`
  have hbound : ∀ i ∈ range L, ∀ j : ℕ, |a i j| ≤
      4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' *
          (1 / ((j : ℝ) + 1) ^ 2) +
        (2 * p) ^ (i + 1) * ((p : ℝ) / 2) * ((i + 1).factorial : ℝ) *
          (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2)) *
          (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (i + 2) else 0) := by
    intro i hi j
    have hiL := mem_range.mp hi
    have hJR : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    have hB := abs_chainPotential_le hp0 i
    have hM : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2) := sum_nonneg fun n _ => by positivity
    have hT1 : 0 ≤ 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' *
        (1 / ((j : ℝ) + 1) ^ 2) := by positivity
    by_cases hdvd : p ∣ j + 1
    · -- crude bound on the multiples of `p`
      rw [if_pos hdvd]
      have hcrude : |a i j| ≤ (2 * p) ^ (i + 1) * ((p : ℝ) / 2) * ((i + 1).factorial : ℝ) *
          (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2)) * (1 / ((j : ℝ) + 1) ^ (i + 2)) := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        rw [mul_sum, sum_mul]
        refine sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have hw := pronicWeight_le (k := i) (M := (j + 1) * n) (by nlinarith)
        have hw0 := (pronicWeight_pos (k := i) (M := (j + 1) * n) (by nlinarith)).le
        rw [abs_mul, abs_mul, abs_of_nonneg hw0]
        push_cast at hw
        calc |c' n| * (|chainPotential p i ((j + 1) * n)| * pronicWeight i ((j + 1) * n))
            ≤ |c' n| * ((2 * p) ^ (i + 1) * ((p : ℝ) / 2) *
                (((i + 1).factorial : ℝ) / (((j : ℝ) + 1) * n) ^ (i + 2))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hB _) hw hw0 (by positivity)) (abs_nonneg _)
          _ = _ := by rw [mul_pow ((j : ℝ) + 1) (n : ℝ) (i + 2)]; field_simp
      linarith
    · -- `L - i` periodic summations by parts
      rw [if_neg hdvd, mul_zero, add_zero]
      obtain ⟨s, hs⟩ : ∃ s, L - i = s + 1 := ⟨L - i - 1, by omega⟩
      have hcop : Nat.Coprime p (j + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
      set D : ℕ → ℝ := fun n => chainPotential p i ((j + 1) * n)
      have hDper : ∀ n, D (n + p) = D n := chainPotential_mul_periodic hp0 i (j + 1)
      have hD0 : ∑ n ∈ range p, D n = 0 := by
        simp only [D]
        rw [sum_range_comp_mul_of_coprime hp0 hcop (chainPotential_periodic hp0 i),
          sum_range_chainPotential hp0]
      set x : ℕ → ℝ := fun n => c' n * pronicWeight i ((j + 1) * n)
      have hre : a i j = ∑ n ∈ range (N + 1), x n * D n := by
        simp only [a]
        rw [sum_Icc_eq_sum_range_succ _ N (by simp [hzero 0 (Or.inl (Nat.zero_le L))])]
        exact sum_congr rfl fun n _ => by simp only [x, D]; ring
      have habel := abs_sum_mul_periodic_le_iter hp0 s D _ hDper hD0
        (fun n => hB ((j + 1) * n)) x (N + 1)
        (fun n hn => by simp only [x, hzero n (Or.inl (by omega)), zero_mul])
        (fun n hn => by simp only [x, hzero n (Or.inr (by omega)), zero_mul])
      rw [← hs] at habel
      have hw := sum_abs_bdiff_iter_weight_le (N := N) (L := L) (i := i) (S := L - i) (J := j + 1)
        (Nat.succ_pos j) (by omega) (c' := c') fun n hn => hzero n (Or.inl (by omega))
      rw [hre]
      refine habel.trans ?_
      have hJ2 : ((j + 1 : ℕ) : ℝ) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) ^ (i + 2) :=
        pow_le_pow_right₀ (by push_cast; linarith) (by omega)
      have h2 : (2 : ℝ) ^ (L - i) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 * (p : ℝ)) ^ (L - i) * ((2 * p) ^ (i + 1) * ((p : ℝ) / 2)) *
            ∑ n ∈ range (N + 1), |bdiff^[L - i] x n|
          ≤ (2 * (p : ℝ)) ^ (L - i) * ((2 * p) ^ (i + 1) * ((p : ℝ) / 2)) *
              (2 ^ (L - i) * ((L + 1).factorial : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (i + 2) *
                smoothnessNorm N L c') := mul_le_mul_of_nonneg_left hw (by positivity)
        _ = 2 ^ L * (p : ℝ) ^ (L + 2) * (2 ^ (L - i) * ((L + 1).factorial : ℝ) *
              smoothnessNorm N L c') / ((j + 1 : ℕ) : ℝ) ^ (i + 2) := by
            have e : (2 * (p : ℝ)) ^ (L - i) * (2 * p) ^ (i + 1) = 2 ^ (L + 1) * (p : ℝ) ^ (L + 1) := by
              rw [← pow_add, show L - i + (i + 1) = L + 1 by omega, mul_pow]
            have hJ0 : ((j + 1 : ℕ) : ℝ) ^ (i + 2) ≠ 0 := by positivity
            calc (2 * (p : ℝ)) ^ (L - i) * ((2 * p) ^ (i + 1) * ((p : ℝ) / 2)) *
                  (2 ^ (L - i) * ((L + 1).factorial : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (i + 2) *
                    smoothnessNorm N L c')
                = ((2 * (p : ℝ)) ^ (L - i) * (2 * p) ^ (i + 1)) * ((p : ℝ) / 2) *
                    (2 ^ (L - i) * ((L + 1).factorial : ℝ) * smoothnessNorm N L c') /
                      ((j + 1 : ℕ) : ℝ) ^ (i + 2) := by ring
              _ = _ := by rw [e, pow_succ (2 : ℝ) L, pow_succ (p : ℝ) (L + 1)]; ring
        _ ≤ 2 ^ L * (p : ℝ) ^ (L + 2) * (2 ^ L * ((L + 1).factorial : ℝ) *
              smoothnessNorm N L c') / ((j + 1 : ℕ) : ℝ) ^ 2 := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) hJ2
            gcongr
        _ = 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' *
              (1 / ((j : ℝ) + 1) ^ 2) := by
            rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num]
            push_cast
            field_simp
  -- sum over `j`, then over `i`
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hper_i : ∀ i ∈ range L, |∑' j, a i j| ≤
      2 * 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' +
        2 ^ L * (L.factorial : ℝ) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
    intro i hi
    have hiL := mem_range.mp hi
    set C₁ := 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' with hC₁e
    set C₂ := (2 * p) ^ (i + 1) * ((p : ℝ) / 2) * ((i + 1).factorial : ℝ) *
      (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2)) with hC₂e
    have hite : Summable fun j : ℕ => (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (i + 2) else 0) := by
      refine Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) (fun j => ?_)
        hz.summable
      have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      split_ifs
      · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hj (by omega))
      · positivity
    have hsb : Summable fun j : ℕ => C₁ * (1 / ((j : ℝ) + 1) ^ 2) +
        C₂ * (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (i + 2) else 0) :=
      (hz.summable.mul_left C₁).add (hite.mul_left C₂)
    have h1 : |∑' j, a i j| ≤ ∑' j, |a i j| := by
      rw [← Real.norm_eq_abs]
      exact (norm_tsum_le_tsum_norm (hsa i).norm).trans (le_of_eq (tsum_congr fun j => by simp))
    have h2 := Summable.tsum_le_tsum (hbound i hi) (hsa i).abs hsb
    rw [Summable.tsum_add (hz.summable.mul_left C₁) (hite.mul_left C₂), tsum_mul_left, tsum_mul_left,
      hz.tsum_eq] at h2
    have h3 := sum_ite_dvd_inv_pow_le (q := i) hp0
    have hC₁ : 0 ≤ C₁ := by rw [hC₁e]; positivity
    have hC₂ : 0 ≤ C₂ := by
      have : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2) := sum_nonneg fun n _ => by positivity
      rw [hC₂e]; positivity
    have hC₂' : C₂ * (2 / (p : ℝ) ^ (i + 2)) ≤
        2 ^ L * (L.factorial : ℝ) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
      have hMi : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2) ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 :=
        sum_le_sum fun n hn => by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
          exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
            (pow_le_pow_right₀ hn1 (by omega))
      have hfac : ((i + 1).factorial : ℝ) ≤ L.factorial := by
        exact_mod_cast Nat.factorial_le (by omega : i + 1 ≤ L)
      have h2i : (2 : ℝ) ^ (i + 1) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
      have e : C₂ * (2 / (p : ℝ) ^ (i + 2)) = 2 ^ (i + 1) * ((i + 1).factorial : ℝ) *
          ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2) := by
        rw [hC₂e, mul_pow, show i + 2 = (i + 1) + 1 by ring, pow_succ (p : ℝ) (i + 1)]
        field_simp
      rw [e]
      have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (i + 2) := sum_nonneg fun n _ => by positivity
      exact mul_le_mul (mul_le_mul h2i hfac (by positivity) (by positivity)) hMi hS0 (by positivity)
    calc |∑' j, a i j| ≤ ∑' j, |a i j| := h1
      _ ≤ C₁ * (Real.pi ^ 2 / 6) +
          C₂ * ∑' j : ℕ, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ (i + 2) else 0) := h2
      _ ≤ C₁ * 2 + C₂ * (2 / (p : ℝ) ^ (i + 2)) := by gcongr
      _ ≤ 2 * 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) * smoothnessNorm N L c' +
          2 ^ L * (L.factorial : ℝ) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
        linarith
  calc |∑ i ∈ range L, ∑' j, a i j| ≤ ∑ i ∈ range L, |∑' j, a i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range L, (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (p : ℝ) ^ (L + 2) *
          smoothnessNorm N L c' + 2 ^ L * (L.factorial : ℝ) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) :=
        sum_le_sum hper_i
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ## §4. The smooth-row law of every order -/

/-- **Smooth large-scale rows of every order.** For rows `c` on primes and `c'` supported in
`[L+1, N]`,
`|B + m R' + β H'| ≤ 2(L+1) 4^L (L+1)! Σ_p |c(p)| (p^{L+1} 𝒮_L(c') + p⁻¹ Σ_n |c'(n)|/n²)`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_smoothnessNorm (N L : ℕ) {c c' : ℕ → ℝ}
    (hc : ∀ d, c d ≠ 0 → d.Prime) (hc' : ∀ n, c' n ≠ 0 → L + 1 ≤ n ∧ n ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      2 * (L + 1) * 4 ^ L * ((L + 1).factorial : ℝ) *
        ∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ (L + 1) * smoothnessNorm N L c' +
          (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) / d) := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_potentialTerms_le N L c c'
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'
  set 𝒮 := smoothnessNorm N L c'
  set M₂ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  have h𝒮 : 0 ≤ 𝒮 := sum_nonneg fun t _ => sum_nonneg fun n _ => by positivity
  have hM₂ : 0 ≤ M₂ := sum_nonneg fun n _ => by positivity
  -- the remainder of the law is the `t = 0` part of the smoothness norm
  have hrem : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2) ≤ 𝒮 := by
    simp only [𝒮, smoothnessNorm]
    have := single_le_sum (f := fun t => ∑ n ∈ Icc 1 N, |bdiff^[t] c' n| / (n : ℝ) ^ (L + 2 - t))
      (fun t _ => sum_nonneg fun n _ => by positivity) (mem_range.mpr (Nat.succ_pos L))
    simpa using this
  -- the potential terms, prime by prime
  set P := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * potentialTerms d n L
  have hP : |P| ≤ ∑ d ∈ Icc 1 N, |c d| * (L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) *
      (d : ℝ) ^ (L + 1) * 𝒮 + 2 ^ L * (L.factorial : ℝ) * M₂ / d)) := by
    have e : P = ∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n * potentialTerms d n L := by
      simp only [P]
      rw [sum_comm]
      refine sum_congr rfl fun d _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    by_cases hcd : c d = 0
    · simp [hcd]
    have hp := hc d hcd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hp.pos
    have h := abs_sum_mul_potentialTerms_le hp hc'
    rw [abs_mul, abs_div, abs_of_pos hdR]
    calc |c d| / d * |∑ n ∈ Icc 1 N, c' n * potentialTerms d n L|
        ≤ |c d| / d * (L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 2) * 𝒮 +
            2 ^ L * (L.factorial : ℝ) * M₂)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = |c d| * (L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮 +
            2 ^ L * (L.factorial : ℝ) * M₂ / d)) := by
          rw [show L + 2 = (L + 1) + 1 by ring, pow_succ (d : ℝ) (L + 1)]; field_simp
  -- assemble
  have hlaw' : |E - P| ≤ ∑ d ∈ Icc 1 N, |c d| * (2 ^ L * ((L + 1).factorial : ℝ) *
      (d : ℝ) ^ (L + 1) * 𝒮) := by
    refine hlaw.trans ?_
    have h0 : 0 ≤ 2 ^ L * ((L + 1).factorial : ℝ) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1) :=
      by positivity
    calc 2 ^ L * ((L + 1).factorial : ℝ) * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1)) *
          ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)
        ≤ 2 ^ L * ((L + 1).factorial : ℝ) * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1)) * 𝒮 :=
          mul_le_mul_of_nonneg_left hrem h0
      _ = ∑ d ∈ Icc 1 N, |c d| * (2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮) := by
          rw [mul_sum, sum_mul]
          exact sum_congr rfl fun d _ => by ring
  have hE : |E| ≤ |P| + |E - P| := by
    have := abs_add_le P (E - P); rwa [add_sub_cancel] at this
  rw [mul_sum]
  refine hE.trans ((add_le_add hP hlaw').trans ?_)
  rw [← sum_add_distrib]
  refine sum_le_sum fun d hd => ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
  have hdR : (0 : ℝ) < d := by linarith
  have hfac : (L.factorial : ℝ) ≤ ((L + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ L)
  have h24 : (2 : ℝ) ^ L ≤ 4 ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hA : 0 ≤ (d : ℝ) ^ (L + 1) * 𝒮 := by positivity
  have hB : 0 ≤ M₂ / d := by positivity
  have hc0 := abs_nonneg (c d)
  have hF : (0 : ℝ) < ((L + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  set A := (d : ℝ) ^ (L + 1) * 𝒮
  set X := 2 * 4 ^ L * ((L + 1).factorial : ℝ)
  have hX : 0 ≤ X := by positivity
  have u1 : 2 ^ L * (L.factorial : ℝ) ≤ X := by
    have : (0 : ℝ) ≤ 2 ^ L := by positivity
    nlinarith [mul_le_mul h24 hfac (by positivity) (by positivity), pow_pos (by norm_num : (0 : ℝ) < 4) L]
  have u2 : 2 ^ L * ((L + 1).factorial : ℝ) ≤ X := by
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) L]
  have key : L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮 +
      2 ^ L * (L.factorial : ℝ) * M₂ / d) + 2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮 ≤
      2 * (L + 1) * 4 ^ L * ((L + 1).factorial : ℝ) * ((d : ℝ) ^ (L + 1) * 𝒮 + M₂ / d) := by
    calc L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮 +
          2 ^ L * (L.factorial : ℝ) * M₂ / d) + 2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮
        = L * X * A + L * (2 ^ L * (L.factorial : ℝ)) * (M₂ / d) +
            2 ^ L * ((L + 1).factorial : ℝ) * A := by simp only [A, X]; ring
      _ ≤ L * X * A + L * X * (M₂ / d) + X * A :=
          add_le_add (add_le_add le_rfl
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hL) hB))
            (mul_le_mul_of_nonneg_right u2 hA)
      _ ≤ 2 * (L + 1) * 4 ^ L * ((L + 1).factorial : ℝ) * ((d : ℝ) ^ (L + 1) * 𝒮 + M₂ / d) := by
          have e : 2 * (L + 1) * 4 ^ L * ((L + 1).factorial : ℝ) * ((d : ℝ) ^ (L + 1) * 𝒮 + M₂ / d) =
              (L + 1) * X * (A + M₂ / d) := by simp only [A, X]; ring
          rw [e]
          nlinarith [mul_nonneg hX hB]
  calc |c d| * (L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮 +
        2 ^ L * (L.factorial : ℝ) * M₂ / d)) +
        |c d| * (2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮)
      = |c d| * (L * (2 * 4 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮 +
          2 ^ L * (L.factorial : ℝ) * M₂ / d) +
          2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 1) * 𝒮) := by ring
    _ ≤ |c d| * (2 * (L + 1) * 4 ^ L * ((L + 1).factorial : ℝ) * ((d : ℝ) ^ (L + 1) * 𝒮 + M₂ / d)) :=
        mul_le_mul_of_nonneg_left key hc0
    _ = 2 * (L + 1) * 4 ^ L * ((L + 1).factorial : ℝ) *
          (|c d| * ((d : ℝ) ^ (L + 1) * 𝒮 + M₂ / d)) := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
