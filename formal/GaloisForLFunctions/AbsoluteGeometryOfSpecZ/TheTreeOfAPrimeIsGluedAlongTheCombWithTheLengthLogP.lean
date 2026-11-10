import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCountertermPaysForTheContactsAtTheSupremumOfTheirSymbol

/-!
# The tree of a prime is glued along the comb with the length `log p`

The counterterm of the comb of the integers is a sum over the primes: `log n = Σ_p v_p(n) log p`.
The summand of `p` is the Busemann function of the tree of `p` at the vertex of depth `v_p(n)`,
for trees with edges of length `log p`; the contacts of `p` have the same weight `log p` on each
pair of points of a chain `{m, mp, mp², …}`. Glue the tree of one prime with another edge length
`ℓ`: contacts of weight `ℓ` along the chains of `p`, and the counterterm
`log(n/2π) − (log p − ℓ) v_p(n)`. The archimedean fibre is not changed: the jets and the constant
`2π`.

* **Sums over the multiples of an integer** (`tendsto_degreeSum_multiples`): on the degree points
  of a window the multiples of `q` carry the fraction `1/q` of a sum.
* **The mean of the Busemann function** (`tendsto_busemannMass`): on a packet,
  `Σ v_p(n) f_n²/n` tends to `∫f²/(p − 1)`.
* **The pairing of the glued tree** (`tendsto_treePairing`): it tends to `2 d₁ d₂` minus the
  functional of the pair `δ = (ℓ − log p)·1_{p^k}`, `c = (ℓ − log p)/(p − 1)`.
* **The edge length is forced** (`treeBezout_iff`): Bézout holds for the glued tree iff the
  Riemann hypothesis holds and `ℓ = log p`. For `ℓ > log p` the symbol of the contacts at `τ = 0`
  exceeds the constant; for `ℓ < log p` the constant is negative.

So a gluing of the trees to the archimedean fibre along the comb of the integers has no modulus
at any prime: the inequality reads the edge lengths from the jets, as it reads the contact orders
and the constant. The glued form with the lengths `log p` is the pairing of the degree points
itself.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {f : ℝ → ℝ}

/-! ### Blocks of length `q` -/

/-- A sum over `[0, qM)` in blocks of length `q`. -/
theorem sum_range_mul_eq_sum_blocks (φ : ℕ → ℝ) (q M : ℕ) :
    ∑ n ∈ range (q * M), φ n = ∑ m ∈ range M, ∑ r ∈ range q, φ (q * m + r) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- In a block of length `q` only the first point is a multiple of `q`. -/
theorem sum_range_mul_ite_dvd (φ : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ∑ n ∈ range (q * M), (if q ∣ n then φ n else 0) = ∑ m ∈ range M, φ (q * m) := by
  rw [sum_range_mul_eq_sum_blocks]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single 0]
  · simp
  · intro r hr hr0
    have hlt : r < q := Finset.mem_range.mp hr
    have hnd : ¬ q ∣ q * m + r := fun h =>
      hr0 (Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_right (dvd_mul_right q m)).mp h) hlt)
    rw [if_neg hnd]
  · intro h
    exact absurd (Finset.mem_range.mpr hq) h

/-- If `φ` varies by at most `ε` inside each block, its sum over `[0, qM)` is `q` times its sum
over the multiples of `q`, up to `M q ε`. -/
theorem abs_sum_range_mul_sub_le (φ : ℕ → ℝ) (q M : ℕ) {ε : ℝ}
    (h : ∀ m r, r < q → |φ (q * m + r) - φ (q * m)| ≤ ε) :
    |∑ n ∈ range (q * M), φ n - q * ∑ m ∈ range M, φ (q * m)| ≤ M * (q * ε) := by
  rw [sum_range_mul_eq_sum_blocks, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ m ∈ range M, (∑ r ∈ range q, φ (q * m + r) - q * φ (q * m))|
      ≤ ∑ m ∈ range M, |∑ r ∈ range q, φ (q * m + r) - q * φ (q * m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ range M, (q : ℝ) * ε := Finset.sum_le_sum fun m _ => by
        have e : ∑ r ∈ range q, φ (q * m + r) - q * φ (q * m) =
            ∑ r ∈ range q, (φ (q * m + r) - φ (q * m)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [e]
        calc |∑ r ∈ range q, (φ (q * m + r) - φ (q * m))|
            ≤ ∑ r ∈ range q, |φ (q * m + r) - φ (q * m)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ r ∈ range q, ε := Finset.sum_le_sum fun r hr => h m r (Finset.mem_range.mp hr)
          _ = (q : ℝ) * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = M * (q * ε) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Sums over the multiples of an integer in a window -/

/-- The term of a sum over the degree points at the scale `N`. -/
def degreeTerm (G : ℝ → ℝ) (N n : ℕ) : ℝ := G (Real.log ((n : ℝ) / N)) / n

theorem degreeTerm_eq_zero_of_le {G : ℝ → ℝ} (h0 : ∀ u, u ≤ 0 → G u = 0) {N n : ℕ}
    (hn : n ≤ N) : degreeTerm G N n = 0 := by
  have hlog : Real.log ((n : ℝ) / N) ≤ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · refine Real.log_nonpos (by positivity) ?_
      rw [div_le_one (by exact_mod_cast (hpos.trans_le hn))]
      exact_mod_cast hn
  rw [degreeTerm, h0 _ hlog, zero_div]

theorem degreeTerm_eq_zero_of_gt {G : ℝ → ℝ} {L : ℕ}
    (h1 : ∀ u, Real.log (1 + L) ≤ u → G u = 0) {N n : ℕ} (hN : 0 < N) (hn : N + L * N < n) :
    degreeTerm G N n = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (1 + (L : ℝ)) ≤ Real.log ((n : ℝ) / N) := by
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ hN']
    have h : ((N + L * N : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.le
    push_cast at h
    linarith
  rw [degreeTerm, h1 _ hlog, zero_div]

/-- Between two points `x ≤ y` the terms of a bounded Lipschitz function differ by at most
`(Lip + sup)(y − x)/x²`. -/
theorem abs_degreeTerm_sub_le {G : ℝ → ℝ} {Lp B : ℝ} (hLp : 0 ≤ Lp)
    (hLip : ∀ u v, |G u - G v| ≤ Lp * |u - v|) (hB : ∀ u, |G u| ≤ B) {N x y : ℕ} (hN : 0 < N)
    (hx : 0 < x) (hxy : x ≤ y) :
    |degreeTerm G N y - degreeTerm G N x| ≤ (Lp + B) * (((y : ℝ) - x) / (x : ℝ) ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hy' : (0 : ℝ) < y := hx'.trans_le hxy'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hd : (0 : ℝ) ≤ y - x := sub_nonneg.mpr hxy'
  -- the displacement of the logarithms is at most `(y − x)/x`
  have hquot : (y : ℝ) / N / ((x : ℝ) / N) = y / x := by field_simp
  have hlog : Real.log ((y : ℝ) / N) - Real.log ((x : ℝ) / N) = Real.log ((y : ℝ) / x) := by
    rw [← Real.log_div (div_pos hy' hN').ne' (div_pos hx' hN').ne', hquot]
  have hlog0 : 0 ≤ Real.log ((y : ℝ) / x) :=
    Real.log_nonneg (by rw [le_div_iff₀ hx']; linarith)
  have hlog1 : Real.log ((y : ℝ) / x) ≤ ((y : ℝ) - x) * (x : ℝ)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy' hx')
    have e : (y : ℝ) / x - 1 = ((y : ℝ) - x) * (x : ℝ)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hx'.ne', div_eq_mul_inv]
    linarith
  have hG : |G (Real.log ((y : ℝ) / N)) - G (Real.log ((x : ℝ) / N))| ≤
      Lp * (((y : ℝ) - x) * (x : ℝ)⁻¹) := by
    refine (hLip _ _).trans (mul_le_mul_of_nonneg_left ?_ hLp)
    rw [hlog, abs_of_nonneg hlog0]
    exact hlog1
  have ha0 : (0 : ℝ) < (x : ℝ)⁻¹ := inv_pos.mpr hx'
  have hb0 : (0 : ℝ) < (y : ℝ)⁻¹ := inv_pos.mpr hy'
  have hba : (y : ℝ)⁻¹ ≤ (x : ℝ)⁻¹ := inv_anti₀ hx' hxy'
  have hab : (x : ℝ)⁻¹ - (y : ℝ)⁻¹ = ((y : ℝ) - x) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) := by
    have h1 : (x : ℝ)⁻¹ * x = 1 := inv_mul_cancel₀ hx'.ne'
    have h2 : (y : ℝ)⁻¹ * y = 1 := inv_mul_cancel₀ hy'.ne'
    calc (x : ℝ)⁻¹ - (y : ℝ)⁻¹
        = (x : ℝ)⁻¹ * ((y : ℝ)⁻¹ * y) - (x : ℝ)⁻¹ * x * (y : ℝ)⁻¹ := by rw [h1, h2]; ring
      _ = ((y : ℝ) - x) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) := by ring
  have hdecomp : degreeTerm G N y - degreeTerm G N x =
      (G (Real.log ((y : ℝ) / N)) - G (Real.log ((x : ℝ) / N))) * (y : ℝ)⁻¹ +
        -(G (Real.log ((x : ℝ) / N)) * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹)) := by
    unfold degreeTerm
    ring
  have hle : ((y : ℝ) - x) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) ≤
      ((y : ℝ) - x) * ((x : ℝ)⁻¹ * (x : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hba ha0.le) hd
  rw [hdecomp]
  calc |(G (Real.log ((y : ℝ) / N)) - G (Real.log ((x : ℝ) / N))) * (y : ℝ)⁻¹ +
          -(G (Real.log ((x : ℝ) / N)) * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹))|
      ≤ |(G (Real.log ((y : ℝ) / N)) - G (Real.log ((x : ℝ) / N))) * (y : ℝ)⁻¹| +
          |-(G (Real.log ((x : ℝ) / N)) * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹))| := abs_add_le _ _
    _ = |G (Real.log ((y : ℝ) / N)) - G (Real.log ((x : ℝ) / N))| * (y : ℝ)⁻¹ +
          |G (Real.log ((x : ℝ) / N))| * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
        rw [abs_neg, abs_mul, abs_mul, abs_of_pos hb0, abs_of_nonneg (sub_nonneg.mpr hba)]
    _ ≤ Lp * (((y : ℝ) - x) * (x : ℝ)⁻¹) * (y : ℝ)⁻¹ +
          B * (((y : ℝ) - x) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹)) := by
        refine add_le_add (mul_le_mul_of_nonneg_right hG hb0.le) ?_
        rw [hab]
        exact mul_le_mul_of_nonneg_right (hB _) (mul_nonneg hd (mul_pos ha0 hb0).le)
    _ = (Lp + B) * (((y : ℝ) - x) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹)) := by ring
    _ ≤ (Lp + B) * (((y : ℝ) - x) * ((x : ℝ)⁻¹ * (x : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hle (add_nonneg hLp hB0)
    _ = (Lp + B) * (((y : ℝ) - x) / (x : ℝ) ^ 2) := by rw [div_eq_mul_inv, pow_two, mul_inv]

/-- **Sums over the multiples of an integer.** On the degree points of a window the multiples of
`q` carry the fraction `1/q` of the sum of a bounded Lipschitz function that vanishes outside the
window. -/
theorem tendsto_degreeSum_multiples {G : ℝ → ℝ} (hG : Continuous G) {Lp B : ℝ} (hLp : 0 ≤ Lp)
    (hLip : ∀ u v, |G u - G v| ≤ Lp * |u - v|) (hB : ∀ u, |G u| ≤ B) {L : ℕ} (hL : 1 ≤ L)
    (h0 : ∀ u, u ≤ 0 → G u = 0) (h1 : ∀ u, Real.log (1 + L) ≤ u → G u = 0) {q : ℕ}
    (hq : 0 < q) :
    Tendsto (fun N : ℕ => ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), degreeTerm G N n)
      atTop (𝓝 ((q : ℝ)⁻¹ * ∫ u in (0 : ℝ)..Real.log (1 + L), G u)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hS := tendsto_degreeSum hG hL
  -- the whole sum is `q` times the sum over the multiples, up to `O(1/N)`
  have hbound : ∀ᶠ N : ℕ in atTop,
      dist (∑ n ∈ Ioc N (N + L * N), G (Real.log ((n : ℝ) / N)) / n)
        (q * ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), degreeTerm G N n) ≤
      (2 + L) * ((Lp + B) * (4 * q)) / N := by
    filter_upwards [eventually_ge_atTop (2 * q)] with N hN
    have hN0 : 0 < N := by omega
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    set M := (N + L * N) / q + 1 with hM
    have hqM : N + L * N < q * M := Nat.lt_mul_div_succ _ hq
    have hsub : Ioc N (N + L * N) ⊆ range (q * M) := fun n hn =>
      Finset.mem_range.mpr (lt_of_le_of_lt (Finset.mem_Ioc.mp hn).2 hqM)
    have hvan : ∀ n ∈ range (q * M), n ∉ Ioc N (N + L * N) → degreeTerm G N n = 0 := by
      intro n _ hn
      by_cases hle : n ≤ N
      · exact degreeTerm_eq_zero_of_le h0 hle
      · exact degreeTerm_eq_zero_of_gt h1 hN0 (by
          by_contra hcon
          exact hn (Finset.mem_Ioc.mpr ⟨not_le.mp hle, not_lt.mp hcon⟩))
    have e1 : ∑ n ∈ Ioc N (N + L * N), G (Real.log ((n : ℝ) / N)) / n =
        ∑ n ∈ range (q * M), degreeTerm G N n := Finset.sum_subset hsub hvan
    have e2 : ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), degreeTerm G N n =
        ∑ m ∈ range M, degreeTerm G N (q * m) := by
      rw [Finset.sum_filter, ← sum_range_mul_ite_dvd (degreeTerm G N) hq M]
      exact Finset.sum_subset hsub fun n hn hn' => by rw [hvan n hn hn', ite_self]
    rw [e1, e2, Real.dist_eq]
    have hε : ∀ m r, r < q → |degreeTerm G N (q * m + r) - degreeTerm G N (q * m)| ≤
        (Lp + B) * (4 * q / (N : ℝ) ^ 2) := by
      intro m r hr
      by_cases hle : q * m + r ≤ N
      · rw [degreeTerm_eq_zero_of_le h0 hle, degreeTerm_eq_zero_of_le h0 (by omega : q * m ≤ N),
          sub_zero, abs_zero]
        exact mul_nonneg (add_nonneg hLp hB0) (by positivity)
      · have hx : 0 < q * m := by omega
        have h2x : N ≤ 2 * (q * m) := by omega
        refine (abs_degreeTerm_sub_le hLp hLip hB hN0 hx (Nat.le_add_right _ _)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (add_nonneg hLp hB0)
        have hx' : (0 : ℝ) < ((q * m : ℕ) : ℝ) := by exact_mod_cast hx
        have hr' : (((q * m + r : ℕ) : ℝ) - ((q * m : ℕ) : ℝ)) ≤ q := by
          have hrq : (r : ℝ) ≤ q := by exact_mod_cast hr.le
          push_cast
          linarith
        have h2x' : (N : ℝ) ≤ 2 * ((q * m : ℕ) : ℝ) := by exact_mod_cast h2x
        rw [div_le_div_iff₀ (pow_pos hx' 2) (pow_pos hN' 2)]
        have h4 := mul_le_mul hr' (pow_le_pow_left₀ hN'.le h2x' 2) (by positivity) hq'.le
        linarith [h4]
    refine (abs_sum_range_mul_sub_le (degreeTerm G N) q M hε).trans ?_
    have hMq : M * q ≤ (2 + L) * N := by
      have h := Nat.div_mul_le_self (N + L * N) q
      have e : M * q = (N + L * N) / q * q + q := by rw [hM]; ring
      have e' : (2 + L) * N = N + L * N + N := by ring
      rw [e, e']
      omega
    have hMq' : (M : ℝ) * q ≤ (2 + L) * N := by exact_mod_cast hMq
    have hNN : (N : ℝ) * ((N : ℝ) ^ 2)⁻¹ = (N : ℝ)⁻¹ := by
      rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN'.ne', one_mul]
    calc (M : ℝ) * (q * ((Lp + B) * (4 * q / (N : ℝ) ^ 2)))
        = ((M : ℝ) * q) * ((Lp + B) * (4 * q / (N : ℝ) ^ 2)) := by ring
      _ ≤ ((2 + L) * N) * ((Lp + B) * (4 * q / (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hMq' (mul_nonneg (add_nonneg hLp hB0) (by positivity))
      _ = (2 + L) * ((Lp + B) * (4 * q)) * ((N : ℝ) * ((N : ℝ) ^ 2)⁻¹) := by ring
      _ = (2 + L) * ((Lp + B) * (4 * q)) / N := by rw [hNN, div_eq_mul_inv]
  have hqT : Tendsto (fun N : ℕ => (q : ℝ) *
      ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), degreeTerm G N n) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + L), G u)) :=
    hS.congr_dist (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound
      (tendsto_const_div_atTop_nhds_zero_nat _))
  refine (hqT.const_mul (q : ℝ)⁻¹).congr fun N => ?_
  rw [inv_mul_cancel_left₀ hq'.ne']

/-- The multiples of `q` in a window carry at most the fraction `1/q` of the supremum. -/
theorem abs_sum_filter_dvd_degreeTerm_le {G : ℝ → ℝ} {B : ℝ} (hB : ∀ u, |G u| ≤ B) (L : ℕ)
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) :
    |∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), degreeTerm G N n| ≤
      B * (1 + L) * (q : ℝ)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : ((Ioc N (N + L * N)).filter (fun n => q ∣ n)).card ≤ (N + L * N) / q := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    exact Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le N)))
  have hNN : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN'.ne'
  calc |∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), degreeTerm G N n|
      ≤ ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), |degreeTerm G N n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ (Ioc N (N + L * N)).filter (fun n => q ∣ n), B / N :=
        Finset.sum_le_sum fun n hn => by
          have hnN : (N : ℝ) ≤ n := by
            exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1.le
          rw [degreeTerm, abs_div, abs_of_pos (hN'.trans_le hnN)]
          exact div_le_div₀ hB0 (hB _) hN' hnN
    _ = (((Ioc N (N + L * N)).filter (fun n => q ∣ n)).card : ℝ) * (B / N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N + L * N : ℕ) : ℝ) / q * (B / N) :=
        mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hcard).trans Nat.cast_div_le)
          (div_nonneg hB0 hN'.le)
    _ = B * (1 + L) * (q : ℝ)⁻¹ * ((N : ℝ) * (N : ℝ)⁻¹) := by
        push_cast
        ring
    _ = B * (1 + L) * (q : ℝ)⁻¹ := by rw [hNN, mul_one]

/-! ### The mean of the Busemann function -/

/-- The valuation at `p` counts the powers of `p` that divide. -/
theorem factorization_eq_sum_pow_dvd {p : ℕ} (hp : p.Prime) {n X : ℕ} (hn : 0 < n)
    (hX : n ≤ X) :
    (n.factorization p : ℝ) = ∑ k ∈ range X, if p ^ (k + 1) ∣ n then (1 : ℝ) else 0 := by
  have hv : n.factorization p ≤ X := (Nat.factorization_lt p hn.ne').le.trans hX
  calc (n.factorization p : ℝ) = ∑ _k ∈ range (n.factorization p), (1 : ℝ) := by simp
    _ = ∑ k ∈ range (n.factorization p), if p ^ (k + 1) ∣ n then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun k hk => (if_pos ((hp.pow_dvd_iff_le_factorization hn.ne').mpr
          (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))).symm
    _ = ∑ k ∈ range X, if p ^ (k + 1) ∣ n then (1 : ℝ) else 0 :=
        Finset.sum_subset (Finset.range_mono hv) fun k _ hk => if_neg fun h =>
          hk (Finset.mem_range.mpr
            (Nat.lt_of_succ_le ((hp.pow_dvd_iff_le_factorization hn.ne').mp h)))

/-- The valuation at `p` against the masses of a packet on the degree points of a window: the
Busemann function of the tree of `p` along the comb. -/
def busemannMass (p : ℕ) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ n ∈ Ioc N (N + L * N), (n.factorization p : ℝ) * (degreeSample f N n ^ 2 / n)

/-- The Busemann function is the sum over the levels `p^k` of the multiples of `p^k`. -/
theorem busemannMass_eq_tsum {p : ℕ} (hp : p.Prime) (f : ℝ → ℝ) (L N : ℕ) :
    busemannMass p f L N = ∑' k : ℕ,
      ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => p ^ (k + 1) ∣ n),
        degreeTerm (fun u => f u ^ 2) N n := by
  have hzero : ∀ k ∉ range (N + L * N),
      ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => p ^ (k + 1) ∣ n),
        degreeTerm (fun u => f u ^ 2) N n = 0 := by
    intro k hk
    have hempty : (Ioc N (N + L * N)).filter (fun n => p ^ (k + 1) ∣ n) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun n hn hdvd => ?_
      have hk' : N + L * N ≤ k := not_lt.mp fun h => hk (Finset.mem_range.mpr h)
      have hn0 : 0 < n := by
        have := (Finset.mem_Ioc.mp hn).1
        omega
      have hle := Nat.le_of_dvd hn0 hdvd
      have hlt : k + 1 < p ^ (k + 1) := Nat.lt_pow_self hp.one_lt
      have := (Finset.mem_Ioc.mp hn).2
      omega
    rw [hempty, Finset.sum_empty]
  rw [tsum_eq_sum hzero]
  calc busemannMass p f L N
      = ∑ n ∈ Ioc N (N + L * N), ∑ k ∈ range (N + L * N),
          if p ^ (k + 1) ∣ n then degreeTerm (fun u => f u ^ 2) N n else 0 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : 0 < n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        rw [factorization_eq_sum_pow_dvd hp hn0 (Finset.mem_Ioc.mp hn).2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs
        · rw [one_mul]
          rfl
        · rw [zero_mul]
    _ = ∑ k ∈ range (N + L * N), ∑ n ∈ Ioc N (N + L * N),
          if p ^ (k + 1) ∣ n then degreeTerm (fun u => f u ^ 2) N n else 0 := Finset.sum_comm
    _ = ∑ k ∈ range (N + L * N),
          ∑ n ∈ (Ioc N (N + L * N)).filter (fun n => p ^ (k + 1) ∣ n),
            degreeTerm (fun u => f u ^ 2) N n :=
        Finset.sum_congr rfl fun k _ => (Finset.sum_filter _ _).symm

/-- **The mean of the Busemann function.** On a packet the valuation at `p` against the masses
tends to the mass over `p − 1`. -/
theorem tendsto_busemannMass {p : ℕ} (hp : p.Prime) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (busemannMass p f (3 * K)) atTop (𝓝 ((∫ u, f u ^ 2) / ((p : ℝ) - 1))) := by
  have hδ3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsuppW := window_of_support hK hsupp
  have hL : 1 ≤ 3 * K := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  -- the square of the packet is bounded and Lipschitz, and vanishes outside the window
  obtain ⟨Cf, hCf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by norm_num)
  obtain ⟨Bf, hBf⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 0)
  have hLp0 : (0 : ℝ) ≤ 2 * Bf * Cf := mul_nonneg (mul_nonneg (by norm_num) hBf0) Cf.coe_nonneg
  have hLip : ∀ u v, |f u ^ 2 - f v ^ 2| ≤ 2 * Bf * Cf * |u - v| := fun u v => by
    have h1 : |f u - f v| ≤ Cf * |u - v| := by
      have := hCf.dist_le_mul u v
      rwa [Real.dist_eq, Real.dist_eq] at this
    have h2 : |f u + f v| ≤ 2 * Bf := by
      have h := abs_add_le (f u) (f v)
      have hu := hBf u
      have hv := hBf v
      rw [Real.norm_eq_abs] at hu hv
      linarith
    have e : f u ^ 2 - f v ^ 2 = (f u - f v) * (f u + f v) := by ring
    rw [e, abs_mul]
    calc |f u - f v| * |f u + f v| ≤ (Cf * |u - v|) * (2 * Bf) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg Cf.coe_nonneg (abs_nonneg _))
      _ = 2 * Bf * Cf * |u - v| := by ring
  have hBG : ∀ u, |f u ^ 2| ≤ Bf ^ 2 := fun u => by
    have hu := hBf u
    rw [Real.norm_eq_abs] at hu
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have h0 : ∀ u, u ≤ 0 → f u ^ 2 = 0 := fun u hu => by
    rw [hsupp u (Or.inl (hu.trans hδ3.le)), zero_pow two_ne_zero]
  have h1 : ∀ u, Real.log (1 + ((3 * K : ℕ) : ℝ)) ≤ u → f u ^ 2 = 0 := fun u hu => by
    rw [hsuppW u (Or.inr (by linarith)), zero_pow two_ne_zero]
  set I := ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 with hI
  have hIeq : ∫ u, f u ^ 2 = I := by
    rw [hI, ← packetAutocorr_zero_eq_integral_window hδ3 hsuppW, packetAutocorr]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show f u ^ 2 = f u * f (u + 0)
      rw [add_zero, sq])
  -- dominated convergence over the levels
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hsumb : Summable fun k : ℕ => Bf ^ 2 * (1 + ((3 * K : ℕ) : ℝ)) * ((p : ℝ)⁻¹) ^ (k + 1) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (Bf ^ 2 * (1 + ((3 * K : ℕ) : ℝ)) * (p : ℝ)⁻¹)
    refine h.congr fun k => ?_
    rw [pow_succ]
    ring
  have hlim : ∀ k : ℕ, Tendsto (fun N : ℕ =>
      ∑ n ∈ (Ioc N (N + 3 * K * N)).filter (fun n => p ^ (k + 1) ∣ n),
        degreeTerm (fun u => f u ^ 2) N n) atTop
      (𝓝 ((((p ^ (k + 1) : ℕ) : ℝ))⁻¹ * I)) := fun k =>
    tendsto_degreeSum_multiples (G := fun u => f u ^ 2) (hf.continuous.pow 2) hLp0 hLip hBG hL
      h0 h1 (pow_pos hp.pos (k + 1))
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      ‖∑ n ∈ (Ioc N (N + 3 * K * N)).filter (fun n => p ^ (k + 1) ∣ n),
        degreeTerm (fun u => f u ^ 2) N n‖ ≤
      Bf ^ 2 * (1 + ((3 * K : ℕ) : ℝ)) * ((p : ℝ)⁻¹) ^ (k + 1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN k
    have h := abs_sum_filter_dvd_degreeTerm_le (G := fun u => f u ^ 2) hBG (3 * K)
      (N := N) (q := p ^ (k + 1)) (by omega) (pow_pos hp.pos (k + 1))
    rw [Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    rw [Nat.cast_pow, inv_pow]
  have hT := tendsto_tsum_of_dominated_convergence hsumb hlim hdom
  have hgeom : ∑' k : ℕ, (((p ^ (k + 1) : ℕ) : ℝ))⁻¹ * I = (∫ u, f u ^ 2) / ((p : ℝ) - 1) := by
    have e : (fun k : ℕ => (((p ^ (k + 1) : ℕ) : ℝ))⁻¹ * I) =
        fun k : ℕ => (p : ℝ)⁻¹ * I * ((p : ℝ)⁻¹) ^ k := by
      funext k
      rw [Nat.cast_pow, pow_succ, mul_inv, inv_pow]
      ring
    have hsub : (1 - (p : ℝ)⁻¹) = ((p : ℝ) - 1) * (p : ℝ)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hp0.ne', one_mul]
    rw [e, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hsub, mul_inv, inv_inv, hIeq,
      div_eq_mul_inv]
    calc (p : ℝ)⁻¹ * I * (((p : ℝ) - 1)⁻¹ * p) = I * ((p : ℝ) - 1)⁻¹ * ((p : ℝ)⁻¹ * p) := by ring
      _ = I * ((p : ℝ) - 1)⁻¹ := by rw [inv_mul_cancel₀ hp0.ne', mul_one]
  rw [hgeom] at hT
  exact hT.congr fun N => (busemannMass_eq_tsum hp f (3 * K) N).symm

/-! ### The tree of a prime with another edge length -/

/-- The deviation of the contacts of a tree at `p` whose edges are longer by `t`: the weight `t`
on the positive powers of `p`. -/
def treeDeviation (p : ℕ) (t : ℝ) : ℕ → ℝ := fun n => if ∃ k : ℕ, n = p ^ (k + 1) then t else 0

theorem treeDeviation_self (p : ℕ) (t : ℝ) : treeDeviation p t p = t := by
  rw [treeDeviation, if_pos ⟨0, by simp⟩]

theorem summable_treeDeviation {p : ℕ} (hp : p.Prime) (t : ℝ) :
    Summable fun n => |treeDeviation p t n| / Real.sqrt n := by
  have hinj : Function.Injective fun k : ℕ => p ^ (k + 1) := fun a b h => by
    have := Nat.pow_right_injective hp.two_le h
    omega
  refine (Function.Injective.summable_iff hinj fun n hn => ?_).mp ?_
  · have hne : ¬ ∃ k : ℕ, n = p ^ (k + 1) := fun ⟨k, hk⟩ => hn ⟨k, hk.symm⟩
    simp only [treeDeviation, if_neg hne, abs_zero, zero_div]
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hs : (1 : ℝ) < Real.sqrt p := by
      rw [Real.lt_sqrt (by norm_num)]
      simpa using hp1
    have hr0 : (0 : ℝ) ≤ (Real.sqrt p)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hr1 : (Real.sqrt p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (|t| * (Real.sqrt p)⁻¹)).congr
      fun k => ?_
    have hsq : Real.sqrt (((p ^ (k + 1) : ℕ) : ℝ)) = Real.sqrt p ^ (k + 1) := by
      rw [Nat.cast_pow, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
        Real.mul_self_sqrt (by positivity)]
    show |t| * (Real.sqrt p)⁻¹ * (Real.sqrt p)⁻¹ ^ k =
      |treeDeviation p t (p ^ (k + 1))| / Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ)
    rw [treeDeviation, if_pos ⟨k, rfl⟩, hsq, div_eq_mul_inv, pow_succ, mul_inv, inv_pow]
    ring

/-- Bézout on the comb of the integers with the tree of `p` glued with the edge length `ℓ`: the
contacts along the chains of `p` have the weight `ℓ`, and the counterterm is
`log(n/2π) − (log p − ℓ) v_p(n)`. -/
def TreeBezout (p : ℕ) (ℓ : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
    ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
        (Real.log p - ℓ) * busemannMass p f (3 * K) N +
        2 * weightedContact (fun n => (Λ n : ℝ) + treeDeviation p (ℓ - Real.log p) n) f
          (3 * K) N) atTop (𝓝 l) →
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- **The pairing of the glued tree.** Jets, the contacts of the tree with the edge length `ℓ`
and its counterterm tend to twice the product of the degrees minus the functional of the pair
`δ = (ℓ − log p)·1_{p^k}`, `c = (ℓ − log p)/(p − 1)`. -/
theorem tendsto_treePairing {p : ℕ} (hp : p.Prime) (ℓ : ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
        (Real.log p - ℓ) * busemannMass p f (3 * K) N +
        2 * weightedContact (fun n => (Λ n : ℝ) + treeDeviation p (ℓ - Real.log p) n) f
          (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        pairForm (treeDeviation p (ℓ - Real.log p)) ((ℓ - Real.log p) / ((p : ℝ) - 1)) f)) := by
  have h := (tendsto_degreeForm_add_weightedContact
    (fun n => (Λ n : ℝ) + treeDeviation p (ℓ - Real.log p) n) hf hfc hK hsupp).add
    ((tendsto_busemannMass hp hf hfc hK hsupp).const_mul (Real.log p - ℓ))
  have e : 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        pairForm (treeDeviation p (ℓ - Real.log p)) ((ℓ - Real.log p) / ((p : ℝ) - 1)) f =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
          (_root_.RHTower.weilFullFunctional
            (fun n => (Λ n : ℝ) + treeDeviation p (ℓ - Real.log p) n)
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re +
        (Real.log p - ℓ) * ((∫ u, f u ^ 2) / ((p : ℝ) - 1)) := by
    unfold pairForm
    ring
  rw [e]
  exact h.congr fun N => by ring

/-- Bézout for the glued tree is the positivity of the functional of its pair on all packets. -/
theorem treeBezout_iff_pairForm {p : ℕ} (hp : p.Prime) (ℓ : ℝ) :
    TreeBezout p ℓ ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      0 ≤ pairForm (treeDeviation p (ℓ - Real.log p)) ((ℓ - Real.log p) / ((p : ℝ) - 1)) g := by
  constructor
  · intro h g hg hgc
    obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
    have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
    have hgc' : HasCompactSupport fun u => g (u - s) :=
      hgc.comp_homeomorph (Homeomorph.subRight s)
    have hle := h _ hg' hgc' K hK hsupp _ (tendsto_treePairing hp ℓ hg' hgc' hK hsupp)
    rw [pairForm_translate] at hle
    linarith
  · intro h f hf hfc K hK hsupp l hl
    rw [tendsto_nhds_unique hl (tendsto_treePairing hp ℓ hf hfc hK hsupp)]
    linarith [h f hf hfc]

/-- **The edge length is forced.** Bézout holds on the comb of the integers with the tree of `p`
glued with the edge length `ℓ` iff the Riemann hypothesis holds and `ℓ = log p`. -/
theorem treeBezout_iff {p : ℕ} (hp : p.Prime) (ℓ : ℝ) :
    TreeBezout p ℓ ↔ RiemannHypothesis ∧ ℓ = Real.log p := by
  rw [treeBezout_iff_pairForm hp, ← combBezoutWith_iff_pairForm,
    combBezoutWith_iff (summable_treeDeviation hp _)]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  refine and_congr_right fun _ => ⟨fun hP => ?_, fun hℓ τ => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ℓ - Real.log p := ⟨_, rfl⟩
    rw [← ht] at hP
    have hsum := summable_treeDeviation hp t
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · -- a shorter tree has a negative constant, which forces the deviation to vanish
      have hc : t / ((p : ℝ) - 1) < 0 := div_neg_of_neg_of_pos hneg hpm
      have h0 := _root_.RHTower.eq_zero_of_perturbationSymbol_nonpos hsum
        (fun τ => (hP τ).trans hc.le) hp.two_le
      rw [treeDeviation_self] at h0
      linarith
    · linarith
    · -- a longer tree: the symbol at `τ = 0` is at least `2t/√p > t/(p − 1)`
      exfalso
      have hnn : ∀ n : ℕ, 0 ≤ _root_.RHTower.weightAtom (treeDeviation p t) n (0 / (2 * π)) := by
        intro n
        unfold _root_.RHTower.weightAtom
        split_ifs with h2
        · rw [zero_div, mul_zero, Real.cos_zero]
          have hd : 0 ≤ treeDeviation p t n := by
            unfold treeDeviation
            split_ifs
            · exact hpos.le
            · exact le_rfl
          positivity
        · exact le_rfl
      have hterm : _root_.RHTower.weightAtom (treeDeviation p t) p (0 / (2 * π)) ≤
          _root_.RHTower.perturbationSymbol (treeDeviation p t) 0 :=
        (_root_.RHTower.summable_weightAtom hsum (0 / (2 * π))).le_tsum p fun n _ => hnn n
      have hval : _root_.RHTower.weightAtom (treeDeviation p t) p (0 / (2 * π)) =
          t * (2 / Real.sqrt p) := by
        unfold _root_.RHTower.weightAtom
        rw [if_pos hp.two_le, treeDeviation_self, zero_div, mul_zero, Real.cos_zero]
        ring
      have hlt : Real.sqrt p < 2 * ((p : ℝ) - 1) := by
        have h1 : Real.sqrt p < p := by
          rw [Real.sqrt_lt' hp0]
          nlinarith
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        linarith
      have hgt : 1 / ((p : ℝ) - 1) < 2 / Real.sqrt p := by
        rw [div_lt_div_iff₀ hpm hs]
        linarith
      have hA : t * (2 / Real.sqrt p) ≤ t * (1 / ((p : ℝ) - 1)) := by
        calc t * (2 / Real.sqrt p) ≤ _root_.RHTower.perturbationSymbol (treeDeviation p t) 0 :=
              hval ▸ hterm
          _ ≤ t / ((p : ℝ) - 1) := hP 0
          _ = t * (1 / ((p : ℝ) - 1)) := by ring
      linarith [mul_lt_mul_of_pos_left hgt hpos]
  · rw [hℓ, sub_self, zero_div]
    exact (perturbationSymbol_eq_zero (fun n _ => by
      unfold treeDeviation
      split_ifs <;> rfl) τ).le

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
