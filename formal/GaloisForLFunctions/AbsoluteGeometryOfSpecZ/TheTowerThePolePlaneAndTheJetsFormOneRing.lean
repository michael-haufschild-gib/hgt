import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrbitRingWithABaseIsATowerOfLines
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArchimedeanFibreOfTheSquare

/-!
# The tower of lines, the pole plane and the jets form one ring of sequences

The orbit ring with a base `𝒪_q` is a ring of integer sequences; the pole plane and the jets are
the weight lines `χ_0 = 1`, `χ_1 = (n)` and `τ^j = χ_{−2j}` of real sequences. The shift
`(F_k y)_n = y_{kn}` acts on all of them.

* **The tower is stable under the Frobenius** (`frobenius_orbitNat`, `frobenius_surfaceMap`,
  `frobenius_mem_orbitBaseRing`): `F_k e_d = g·e_{d/g}` with `g = gcd(d, k)`, and
  `F_k P([q]) = P([q]^k)`.
* **One ring** (`towerWeightRing`, `shift_mem_towerWeightRing`): the real algebra `𝒮_q` generated
  by the sequences of `𝒪_q`, by `χ_1` and by `τ` is stable under every shift. It contains the tower
  of lines, the pole plane and the jets, and all the integer weights, since `χ_{−1} = χ_1 τ`.
* **Lines and weights are independent** (`eq_zero_of_weightedSection_eq_zero`): for a base
  `q ≥ 2`, a section `Σ_e χ_e·s_e` with `s_e` a section of the level `M` of the tower vanishes only
  if every polynomial on every line vanishes. On the degrees `n = d(1 + Ms)` the section is
  `d·Σ_e n^e P_{e,d}(qⁿ)`; the top power of `qⁿ` carries an integer polynomial in `n`, which is at
  least `1` in absolute value beyond its roots, and the rest is smaller by the factor
  `n^E/qⁿ` (`eq_zero_of_weighted_eval_eq_zero`).
* **The count** (`card_image_weightedLatticeMap`): the sections of the level `M` with `E + 1`
  consecutive integer weights and `b` digits in `[−A, A]` on each line are
  `(((2A + 1)^b)^{τ(M)})^{E+1}` in number: the count of the tower on each weight line.
-/

open Finset Polynomial Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The Frobenius on the tower -/

theorem frobenius_surfaceMap (q : ℤ) (k : ℕ+) (Q : ℤ[X]) :
    frobenius k (surfaceMap q Q) = surfaceMap q (Q.comp (X ^ (k : ℕ))) := by
  refine ghostRing_ext fun n => ?_
  rw [ghostComponent_frobenius, ghostComponent_surfaceMap, ghostComponent_surfaceMap,
    Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, PNat.mul_coe, pow_mul']

theorem dvd_mul_iff_div_gcd_dvd {d k n : ℕ} (hd : 0 < d) :
    d ∣ k * n ↔ d / Nat.gcd d k ∣ n := by
  have hg := Nat.gcd_pos_of_pos_left k hd
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  constructor
  · intro h
    have h1 : d / Nat.gcd d k * Nat.gcd d k ∣ k / Nat.gcd d k * n * Nat.gcd d k := by
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d k), mul_right_comm,
        Nat.div_mul_cancel (Nat.gcd_dvd_right d k)]
      exact h
    exact hcop.dvd_mul_left.mp ((Nat.mul_dvd_mul_iff_right hg).mp h1)
  · intro h
    have h1 : d / Nat.gcd d k * Nat.gcd d k ∣ n * k := mul_dvd_mul h (Nat.gcd_dvd_right d k)
    rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left d k), mul_comm] at h1

/-- **The Frobenius of an orbit**: `F_k e_d = g·e_{d/g}`, `g = gcd(d, k)`. -/
theorem frobenius_orbitNat (k : ℕ+) {d : ℕ} (hd : 0 < d) :
    frobenius k (orbitNat d) =
      ((Nat.gcd d k : ℕ) : ghostRing) * orbitNat (d / Nat.gcd d k) := by
  have hg : 0 < Nat.gcd d k := Nat.gcd_pos_of_pos_left _ hd
  have hd' : 0 < d / Nat.gcd d k :=
    Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left d k)) hg
  refine ghostRing_ext fun n => ?_
  rw [ghostComponent_frobenius, ghostComponent_orbitNat hd, map_mul, map_natCast,
    ghostComponent_orbitNat hd', PNat.mul_coe]
  by_cases h : d / Nat.gcd d k ∣ (n : ℕ)
  · rw [if_pos ((dvd_mul_iff_div_gcd_dvd hd).mpr h), if_pos h, ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left d k)]
  · rw [if_neg (fun h' => h ((dvd_mul_iff_div_gcd_dvd hd).mp h')), if_neg h, mul_zero]

/-- **The orbit ring with a base is stable under the Frobenius.** -/
theorem frobenius_mem_orbitBaseRing (q : ℤ) (k : ℕ+) {x : ghostRing}
    (hx : x ∈ orbitBaseRing q) : frobenius k x ∈ orbitBaseRing q := by
  obtain ⟨M, hM, P, rfl⟩ := hx
  rw [orbitSection, map_sum]
  refine Subring.sum_mem _ fun d hd => ?_
  have hd0 := Nat.pos_of_mem_divisors hd
  have hg : 0 < Nat.gcd d k := Nat.gcd_pos_of_pos_left _ hd0
  have hd' : 0 < d / Nat.gcd d k :=
    Nat.div_pos (Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d k)) hg
  rw [map_mul, frobenius_orbitNat k hd0, frobenius_surfaceMap, mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _)
    (show orbitNat _ * surfaceMap q _ ∈ orbitBaseRing q from
      orbitNat_mul_surfaceMap_mem q hd' _)

/-! ### One ring of sequences -/

/-- An element of the arithmetic square as a real sequence. -/
def realSeq : ghostRing →+* (ℕ+ → ℝ) :=
  RingHom.pi fun n => (Int.castRingHom ℝ).comp (ghostComponent n)

theorem realSeq_apply (x : ghostRing) (n : ℕ+) : realSeq x n = (ghostComponent n x : ℝ) := rfl

/-- On the square the shift is the Frobenius. -/
theorem shift_realSeq (k : ℕ+) (x : ghostRing) :
    shift k (realSeq x) = realSeq (frobenius k x) := rfl

/-- **The ring of the tower, the pole plane and the jets**: the real algebra of sequences
generated by the orbit ring with a base, the weight line `χ_1` and the jet coordinate `τ`. -/
def towerWeightRing (q : ℤ) : Subalgebra ℝ (ℕ+ → ℝ) :=
  Algebra.adjoin ℝ (realSeq '' (orbitBaseRing q : Set ghostRing) ∪ {weight 1, tau})

theorem realSeq_mem_towerWeightRing (q : ℤ) {x : ghostRing} (hx : x ∈ orbitBaseRing q) :
    realSeq x ∈ towerWeightRing q :=
  Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)

theorem weight_one_mem_towerWeightRing (q : ℤ) : weight 1 ∈ towerWeightRing q :=
  Algebra.subset_adjoin (Or.inr (Or.inl rfl))

theorem tau_mem_towerWeightRing (q : ℤ) : tau ∈ towerWeightRing q :=
  Algebra.subset_adjoin (Or.inr (Or.inr rfl))

/-- The jets `τ^j` lie in the ring. -/
theorem tau_pow_mem_towerWeightRing (q : ℤ) (j : ℕ) : tau ^ j ∈ towerWeightRing q :=
  Subalgebra.pow_mem _ (tau_mem_towerWeightRing q) j

/-- The weight `−1` lies in the ring: `χ_{−1} = χ_1 τ`. -/
theorem weight_neg_one_mem_towerWeightRing (q : ℤ) : weight (-1) ∈ towerWeightRing q := by
  have h : weight (-1) = weight 1 * tau := by
    funext n
    have hn : (((n : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast n.ne_zero
    simp only [weight, tau, Pi.mul_apply, Real.rpow_neg_one, Real.rpow_one]
    field_simp
  rw [h]
  exact Subalgebra.mul_mem _ (weight_one_mem_towerWeightRing q) (tau_mem_towerWeightRing q)

/-- **The ring is stable under every shift.** -/
theorem shift_mem_towerWeightRing (q : ℤ) (k : ℕ+) {y : ℕ+ → ℝ}
    (hy : y ∈ towerWeightRing q) : shift k y ∈ towerWeightRing q := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨x, hx, rfl⟩ | hy
    · rw [shift_realSeq]
      exact realSeq_mem_towerWeightRing q (frobenius_mem_orbitBaseRing q k hx)
    · rcases hy with rfl | hy
      · rw [shift_weight]
        exact Subalgebra.smul_mem _ (weight_one_mem_towerWeightRing q) _
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, shift_tau]
        exact Subalgebra.smul_mem _ (tau_mem_towerWeightRing q) _
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hx hy

/-! ### Exponential polynomials in the degree -/

/-- A polynomial of degree at most `D` against its term of degree `D`. -/
theorem abs_eval_sub_top_mul_le {P : ℤ[X]} {D : ℕ} (hD : P.natDegree ≤ D) {x : ℤ}
    (hx : 1 ≤ x) :
    |P.eval x - P.coeff D * x ^ D| * x ≤ (∑ i ∈ range D, |P.coeff i|) * x ^ D := by
  have hx0 : (0 : ℤ) ≤ x := by omega
  have h := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD) x
  rw [Finset.sum_range_succ] at h
  have h' : P.eval x - P.coeff D * x ^ D = ∑ i ∈ range D, P.coeff i * x ^ i := by
    rw [h]
    ring
  rw [h']
  calc |∑ i ∈ range D, P.coeff i * x ^ i| * x
      ≤ (∑ i ∈ range D, |P.coeff i * x ^ i|) * x :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hx0
    _ = ∑ i ∈ range D, |P.coeff i| * x ^ (i + 1) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 i), pow_succ]
        ring
    _ ≤ ∑ i ∈ range D, |P.coeff i| * x ^ D :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hx (Nat.succ_le_of_lt (Finset.mem_range.mp hi))) (abs_nonneg _)
    _ = (∑ i ∈ range D, |P.coeff i|) * x ^ D := by rw [Finset.sum_mul]

/-- **An exponential polynomial in `n` with infinitely many zeros vanishes.** If
`Σ_{e ≤ E} n^e P_e(qⁿ) = 0` for arbitrarily large `n`, every `P_e` is zero. -/
theorem eq_zero_of_weighted_eval_eq_zero {q : ℕ} (hq : 2 ≤ q) (E : ℕ) (P : ℕ → ℤ[X])
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∑ e ∈ range (E + 1), (n : ℤ) ^ e * (P e).eval ((q : ℤ) ^ n) = 0) :
    ∀ e ∈ range (E + 1), P e = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨e₁, he₁, hP₁⟩ := hne
  -- the largest degree in `qⁿ`
  obtain ⟨D, hDle, e₀, he₀, hc₀⟩ : ∃ D : ℕ, (∀ e ∈ range (E + 1), (P e).natDegree ≤ D) ∧
      ∃ e₀ ∈ range (E + 1), (P e₀).coeff D ≠ 0 := by
    obtain ⟨e₀, he₀, hsup⟩ := Finset.exists_mem_eq_sup (range (E + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos E)⟩ fun e => (P e).natDegree
    refine ⟨(range (E + 1)).sup fun e => (P e).natDegree,
      fun e he => Finset.le_sup (f := fun e => (P e).natDegree) he, ?_⟩
    rcases Nat.eq_zero_or_pos ((range (E + 1)).sup fun e => (P e).natDegree) with hD0 | hDpos
    · refine ⟨e₁, he₁, fun h0 => hP₁ ?_⟩
      have hdeg : (P e₁).natDegree = 0 :=
        Nat.le_zero.mp (hD0 ▸ Finset.le_sup (f := fun e => (P e).natDegree) he₁)
      rw [hD0] at h0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, h0, Polynomial.C_0]
    · refine ⟨e₀, he₀, fun h0 => ?_⟩
      rw [hsup, Polynomial.coeff_natDegree] at h0
      rw [hsup, Polynomial.leadingCoeff_eq_zero.mp h0, Polynomial.natDegree_zero] at hDpos
      exact lt_irrefl 0 hDpos
  -- the coefficient of the top power of `qⁿ`: a polynomial in `n`
  have hLne : (∑ e ∈ range (E + 1), Polynomial.C ((P e).coeff D) * Polynomial.X ^ e : ℤ[X]) ≠
      0 := by
    intro h0
    have hcoeff := congrArg (fun p : ℤ[X] => p.coeff e₀) h0
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single_of_mem e₀ he₀ (fun e _ hne' => by
      rw [if_neg fun h => hne' h.symm]), if_pos rfl] at hcoeff
    exact hc₀ hcoeff
  have hLeval : ∀ n : ℤ,
      (∑ e ∈ range (E + 1), Polynomial.C ((P e).coeff D) * Polynomial.X ^ e : ℤ[X]).eval n =
        ∑ e ∈ range (E + 1), (P e).coeff D * n ^ e := by
    intro n
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      ∑ e ∈ range (E + 1), (P e).coeff D * (n : ℤ) ^ e ≠ 0 := by
    have hfin : {n : ℕ | (∑ e ∈ range (E + 1),
        Polynomial.C ((P e).coeff D) * Polynomial.X ^ e : ℤ[X]).eval (n : ℤ) = 0}.Finite := by
      refine ((∑ e ∈ range (E + 1),
          Polynomial.C ((P e).coeff D) * Polynomial.X ^ e : ℤ[X]).roots.toFinset.finite_toSet.preimage
        (Nat.cast_injective (R := ℤ)).injOn).subset fun n hn => ?_
      rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hLne]
      exact hn
    obtain ⟨b, hb⟩ := hfin.bddAbove
    refine ⟨b + 1, fun n hn h0 => ?_⟩
    have hmem : n ∈ {n : ℕ | (∑ e ∈ range (E + 1),
        Polynomial.C ((P e).coeff D) * Polynomial.X ^ e : ℤ[X]).eval (n : ℤ) = 0} := by
      rw [Set.mem_setOf_eq, hLeval]
      exact h0
    have := hb hmem
    omega
  -- the lower powers of `qⁿ`
  have hB0 : (0 : ℤ) ≤ ∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n →
      (∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i|) * (n : ℤ) ^ E < (q : ℤ) ^ n := by
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
    have hB0' : (0 : ℝ) ≤ ((∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i| : ℤ) : ℝ) := by
      exact_mod_cast hB0
    have hpos : (0 : ℝ) <
        1 / (((∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i| : ℤ) : ℝ) + 1) := by
      positivity
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
      ((tendsto_pow_const_div_const_pow_of_one_lt E hq1).eventually (gt_mem_nhds hpos))
    refine ⟨N₂, fun n hn => ?_⟩
    have h1 := hN₂ n hn
    have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
    rw [div_lt_div_iff₀ hqn (by positivity), one_mul] at h1
    have hnE : (0 : ℝ) ≤ (n : ℝ) ^ E := by positivity
    have h2 : (((∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i| : ℤ) : ℝ)) * (n : ℝ) ^ E <
        (q : ℝ) ^ n := by nlinarith
    exact_mod_cast h2
  obtain ⟨n, hn, hzero⟩ := h (max (max N₁ N₂) 1)
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : N₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn0 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (le_max_right _ _).trans hn
  have hx1 : (1 : ℤ) ≤ (q : ℤ) ^ n := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q))
  have hx0 : (0 : ℤ) < (q : ℤ) ^ n := by omega
  have hsplit : ((q : ℤ) ^ n) ^ D * ∑ e ∈ range (E + 1), (P e).coeff D * (n : ℤ) ^ e =
      -∑ e ∈ range (E + 1), (n : ℤ) ^ e *
        ((P e).eval ((q : ℤ) ^ n) - (P e).coeff D * ((q : ℤ) ^ n) ^ D) := by
    rw [Finset.mul_sum, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← hzero]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hL1 : 1 ≤ |∑ e ∈ range (E + 1), (P e).coeff D * (n : ℤ) ^ e| :=
    Int.one_le_abs (hN₁ n hn1)
  have hbound : ((q : ℤ) ^ n) ^ D * (q : ℤ) ^ n ≤
      ((q : ℤ) ^ n) ^ D *
        ((∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i|) * (n : ℤ) ^ E) := by
    have hxD : (0 : ℤ) ≤ ((q : ℤ) ^ n) ^ D := pow_nonneg hx0.le D
    calc ((q : ℤ) ^ n) ^ D * (q : ℤ) ^ n
        ≤ ((q : ℤ) ^ n) ^ D * |∑ e ∈ range (E + 1), (P e).coeff D * (n : ℤ) ^ e| *
            (q : ℤ) ^ n :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hxD hL1) hx0.le
      _ = |∑ e ∈ range (E + 1), (n : ℤ) ^ e *
            ((P e).eval ((q : ℤ) ^ n) - (P e).coeff D * ((q : ℤ) ^ n) ^ D)| * (q : ℤ) ^ n := by
          rw [← abs_of_nonneg hxD, ← abs_mul, abs_of_nonneg hxD, hsplit, abs_neg]
      _ ≤ (∑ e ∈ range (E + 1), |(n : ℤ) ^ e *
            ((P e).eval ((q : ℤ) ^ n) - (P e).coeff D * ((q : ℤ) ^ n) ^ D)|) * (q : ℤ) ^ n :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hx0.le
      _ = ∑ e ∈ range (E + 1), (n : ℤ) ^ e *
            (|(P e).eval ((q : ℤ) ^ n) - (P e).coeff D * ((q : ℤ) ^ n) ^ D| * (q : ℤ) ^ n) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [abs_mul, abs_of_nonneg (pow_nonneg (by omega : (0 : ℤ) ≤ (n : ℤ)) e)]
          ring
      _ ≤ ∑ e ∈ range (E + 1), (n : ℤ) ^ E *
            ((∑ i ∈ range D, |(P e).coeff i|) * ((q : ℤ) ^ n) ^ D) :=
          Finset.sum_le_sum fun e he => mul_le_mul
            (pow_le_pow_right₀ hn0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp he)))
            (abs_eval_sub_top_mul_le (hDle e he) hx1)
            (mul_nonneg (abs_nonneg _) hx0.le) (pow_nonneg (by omega) E)
      _ = ((q : ℤ) ^ n) ^ D *
            ((∑ e ∈ range (E + 1), ∑ i ∈ range D, |(P e).coeff i|) * (n : ℤ) ^ E) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
  have hle := le_of_mul_le_mul_left hbound (pow_pos hx0 D)
  exact absurd (hN₂ n hn2) (not_lt.mpr hle)

/-! ### Sections with weights -/

/-- A section of the level `M` with the weights `0, …, E`: the section `P e` of the tower on the
weight line `χ_e`. -/
def weightedSection (q : ℤ) (M E : ℕ) (P : ℕ → ℕ → ℤ[X]) : ℕ+ → ℝ :=
  ∑ e ∈ range (E + 1), weight 1 ^ e * realSeq (orbitSection q M (P e))

theorem weightedSection_mem_towerWeightRing (q : ℤ) {M : ℕ} (hM : 0 < M) (E : ℕ)
    (P : ℕ → ℕ → ℤ[X]) : weightedSection q M E P ∈ towerWeightRing q :=
  Subalgebra.sum_mem _ fun e _ => Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ (weight_one_mem_towerWeightRing q) e)
    (realSeq_mem_towerWeightRing q (orbitSection_mem_orbitBaseRing q hM (P e)))

theorem weightedSection_apply (q : ℤ) (M E : ℕ) (P : ℕ → ℕ → ℤ[X]) (n : ℕ+) :
    weightedSection q M E P n =
      ((∑ e ∈ range (E + 1),
        ((n : ℕ) : ℤ) ^ e * ghostComponent n (orbitSection q M (P e)) : ℤ) : ℝ) := by
  simp only [weightedSection, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, weight,
    Real.rpow_one, realSeq_apply]
  push_cast
  rfl

theorem weightedSection_sub (q : ℤ) (M E : ℕ) (P P' : ℕ → ℕ → ℤ[X]) :
    weightedSection q M E (fun e d => P e d - P' e d) =
      weightedSection q M E P - weightedSection q M E P' := by
  simp only [weightedSection, orbitSection_sub, map_sub, mul_sub, Finset.sum_sub_distrib]

/-- **Lines and weights are independent.** For a base `q ≥ 2`, a section with weights that
vanishes has the zero polynomial on every line and every weight. -/
theorem eq_zero_of_weightedSection_eq_zero {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M) (E : ℕ)
    {P : ℕ → ℕ → ℤ[X]} (h : weightedSection (q : ℤ) M E P = 0) :
    ∀ d ∈ M.divisors, ∀ e ∈ range (E + 1), P e d = 0 := by
  have hz : ∀ n : ℕ+, ∑ e ∈ range (E + 1),
      ((n : ℕ) : ℤ) ^ e * ghostComponent n (orbitSection (q : ℤ) M (P e)) = 0 := fun n => by
    have h1 := congrFun h n
    rw [weightedSection_apply, Pi.zero_apply] at h1
    exact_mod_cast h1
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have hdM := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hgcd : ∀ s : ℕ, Nat.gcd M (d * (1 + M * s)) = d := by
      intro s
      obtain ⟨M', rfl⟩ := hdM
      have h1 : Nat.gcd M' (1 + d * M' * s) = 1 := by
        rw [show d * M' * s = M' * (d * s) by ring, Nat.gcd_add_mul_left_right]
        exact Nat.gcd_one_right _
      rw [Nat.gcd_mul_left, h1, mul_one]
    refine eq_zero_of_weighted_eval_eq_zero hq E (fun e => P e d) fun N => ?_
    have hpos : 0 < d * (1 + M * N) := by positivity
    refine ⟨d * (1 + M * N), ?_, ?_⟩
    · calc N ≤ M * N := Nat.le_mul_of_pos_left N hM
        _ ≤ 1 + M * N := Nat.le_add_left _ _
        _ ≤ d * (1 + M * N) := Nat.le_mul_of_pos_left _ hd0
    · have hc := hz ⟨d * (1 + M * N), hpos⟩
      have hterm : ∀ e ∈ range (E + 1),
          ghostComponent ⟨d * (1 + M * N), hpos⟩ (orbitSection (q : ℤ) M (P e)) =
            (d : ℤ) * (P e d).eval ((q : ℤ) ^ (d * (1 + M * N))) := fun e he => by
        rw [ghostComponent_orbitSection _ hM, PNat.mk_coe, hgcd N,
          Finset.sum_eq_single_of_mem d (Nat.mem_divisors_self d hd0.ne') (fun d' hd' hne => by
            have hd'd := Nat.dvd_of_mem_divisors hd'
            have hlt : d' < d := lt_of_le_of_ne (Nat.le_of_dvd hd0 hd'd) hne
            rw [ih d' hlt (Nat.mem_divisors.mpr ⟨hd'd.trans hdM, hM.ne'⟩) e he,
              Polynomial.eval_zero, mul_zero])]
      rw [Finset.sum_congr rfl fun e he => by rw [hterm e he]] at hc
      have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hfac : (d : ℤ) * ∑ e ∈ range (E + 1),
          ((d * (1 + M * N) : ℕ) : ℤ) ^ e * (P e d).eval ((q : ℤ) ^ (d * (1 + M * N))) = 0 := by
        rw [Finset.mul_sum, ← hc]
        exact Finset.sum_congr rfl fun e _ => by
          rw [PNat.mk_coe]
          ring
      exact (mul_eq_zero.mp hfac).resolve_left hd'

/-! ### The count -/

/-- The lattice of sections of the level `M` with the weights `0, …, E` and `b` digits on each
line of each weight. -/
def weightedLatticeMap (q : ℤ) (M E b : ℕ) (c : Fin (E + 1) → ↥M.divisors → Fin b → ℤ) :
    ℕ+ → ℝ :=
  weightedSection q M E fun e d =>
    if he : e < E + 1 then
      (if hd : d ∈ M.divisors then digitPoly (c ⟨e, he⟩ ⟨d, hd⟩) else 0)
    else 0

theorem weightedLatticeMap_injective {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M) (E b : ℕ) :
    Function.Injective (weightedLatticeMap (q : ℤ) M E b) := by
  intro c c' hcc
  have hzero : weightedSection (q : ℤ) M E (fun e d =>
      (if he : e < E + 1 then
        (if hd : d ∈ M.divisors then digitPoly (c ⟨e, he⟩ ⟨d, hd⟩) else 0) else 0) -
      (if he : e < E + 1 then
        (if hd : d ∈ M.divisors then digitPoly (c' ⟨e, he⟩ ⟨d, hd⟩) else 0) else 0)) = 0 := by
    rw [weightedSection_sub]
    exact sub_eq_zero.mpr hcc
  have hP := eq_zero_of_weightedSection_eq_zero hq hM E hzero
  funext ⟨e, he⟩ ⟨d, hd⟩ j
  have h := hP d hd e (Finset.mem_range.mpr he)
  rw [dif_pos he, dif_pos he, dif_pos hd, dif_pos hd, sub_eq_zero] at h
  rw [← coeff_digitPoly (c ⟨e, he⟩ ⟨d, hd⟩) j, ← coeff_digitPoly (c' ⟨e, he⟩ ⟨d, hd⟩) j, h]

open Classical in
/-- **The count of the sections with weights**: `b` digits in `[−A, A]` on each of the `τ(M)`
lines of each of the `E + 1` weights. -/
theorem card_image_weightedLatticeMap {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M) (A E b : ℕ) :
    ((Fintype.piFinset fun _ : Fin (E + 1) => Fintype.piFinset fun _ : ↥M.divisors =>
        Fintype.piFinset fun _ : Fin b => Finset.Icc (-(A : ℤ)) A).image
      (weightedLatticeMap (q : ℤ) M E b)).card =
      (((2 * A + 1) ^ b) ^ M.divisors.card) ^ (E + 1) := by
  have hcard : (Finset.Icc (-(A : ℤ)) A).card = 2 * A + 1 := by
    rw [Int.card_Icc]
    omega
  rw [Finset.card_image_of_injective _ (weightedLatticeMap_injective hq hM E b),
    Fintype.card_piFinset]
  simp [Fintype.card_piFinset, hcard]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
