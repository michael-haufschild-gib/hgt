import GaloisForLFunctions.HTGeometry.ExponentialLatticeWeight
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries

/-!
# The polynomial lattice weight and its exact summability threshold

For the `ℓ¹` bracket `⟨ν⟩ = 1 + |ν|₁` on `ℤ^d`, the radial polynomial weight `⟨ν⟩^{-s}` is summable
exactly above the dimension:

`Σ_{ν ∈ ℤ^d} ⟨ν⟩^{-s} < ∞  ⟺  d < s`.

Sufficiency is the weighted arithmetic–geometric inequality: `(∏_i (1+|ν_i|))^{1/d} ≤ ⟨ν⟩`, so the
weight is dominated by the product weight `∏_i (1+|ν_i|)^{-s/d}`, whose sum is the `d`-th power of a
one-dimensional `p`-series with exponent `s/d > 1`.

Necessity is a cube-annulus count: between the cubes of half-side `N` and `2N` there are at least
`N^d` lattice points, each of bracket at most `4dN`, so every annulus carries at least the fixed
mass `(4d)^{-s}` as soon as `s ≤ d`.  Nesting the annuli of half-side `2^k` makes the partial sums
unbounded.
-/

open Filter Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `ℓ¹` bracket of a lattice point. -/
def latticeBracket {d : ℕ} (ν : Fin d → ℤ) : ℝ := 1 + latticeEll1 ν

theorem one_le_latticeBracket {d : ℕ} (ν : Fin d → ℤ) : 1 ≤ latticeBracket ν := by
  rw [latticeBracket]
  linarith [latticeEll1_nonneg ν]

theorem latticeBracket_pos {d : ℕ} (ν : Fin d → ℤ) : 0 < latticeBracket ν :=
  lt_of_lt_of_le zero_lt_one (one_le_latticeBracket ν)

section OneDimensional

/-- The one-dimensional bracket weight is summable above exponent one. -/
theorem summable_int_bracket_rpow {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-t)) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-t)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-t)) := Real.summable_nat_rpow.mpr (by linarith)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr fun n => ?_
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun n => ?_
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    ring_nf
  · refine hnat.congr fun n => ?_
    rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    ring_nf

end OneDimensional

section Product

set_option maxHeartbeats 1000000 in
/-- The product weight is summable on `ℤ^d` above exponent one in each coordinate. -/
theorem summable_prod_bracket_rpow (d : ℕ) {t : ℝ} (ht : 1 < t) :
    Summable (fun ν : Fin d → ℤ => ∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ (-t)) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
      have hprod : Summable
          (fun p : ℤ × (Fin d → ℤ) =>
            (1 + |((p.1 : ℤ) : ℝ)|) ^ (-t) * ∏ i, (1 + |((p.2 i : ℤ) : ℝ)|) ^ (-t)) :=
        Summable.mul_of_nonneg (summable_int_bracket_rpow ht) ih
          (fun _ => Real.rpow_nonneg (by positivity) _)
          (fun _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _)
      refine (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ))).mp ?_
      refine hprod.congr fun p => ?_
      show (1 + |((p.1 : ℤ) : ℝ)|) ^ (-t) * ∏ i, (1 + |((p.2 i : ℤ) : ℝ)|) ^ (-t)
        = ∏ i, (1 + |(((Fin.cons p.1 p.2 : Fin (d + 1) → ℤ) i : ℤ) : ℝ)|) ^ (-t)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

end Product

section Sufficiency

/-- **The arithmetic–geometric comparison.**  The geometric mean of the coordinate brackets never
exceeds the `ℓ¹` bracket. -/
theorem geom_mean_le_latticeBracket {d : ℕ} (hd : 0 < d) (ν : Fin d → ℤ) :
    ∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ ((d : ℝ)⁻¹) ≤ latticeBracket ν := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin d)), (0 : ℝ) ≤ (d : ℝ)⁻¹ := fun _ _ => by positivity
  have hw' : ∑ _i ∈ (Finset.univ : Finset (Fin d)), (d : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin d)), (0 : ℝ) ≤ 1 + |((ν i : ℤ) : ℝ)| :=
    fun _ _ => by positivity
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin d))
    (fun _ => (d : ℝ)⁻¹) (fun i => 1 + |((ν i : ℤ) : ℝ)|) hw hw' hz
  refine le_trans hgm ?_
  have hsum : ∑ i, (d : ℝ)⁻¹ * (1 + |((ν i : ℤ) : ℝ)|)
      = 1 + (d : ℝ)⁻¹ * latticeEll1 ν := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, latticeEll1]
    field_simp
  rw [hsum, latticeBracket]
  have hE : 0 ≤ latticeEll1 ν := latticeEll1_nonneg ν
  have hinv : (d : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast hd
  nlinarith [hE, hinv]

/-- **Sufficiency.**  Above the dimension the radial polynomial lattice weight is summable. -/
theorem summable_latticeBracket_rpow {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) < s) :
    Summable (fun ν : Fin d → ℤ => latticeBracket ν ^ (-s)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs0 : 0 < s := lt_trans hdR hs
  have ht : 1 < s / (d : ℝ) := (one_lt_div hdR).mpr hs
  refine Summable.of_nonneg_of_le
    (fun ν => Real.rpow_nonneg (latticeBracket_pos ν).le _) ?_
    (summable_prod_bracket_rpow d ht)
  intro ν
  have hgm := geom_mean_le_latticeBracket hd ν
  have hpos : (0 : ℝ) < ∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ ((d : ℝ)⁻¹) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (by positivity) _
  have hstep : latticeBracket ν ^ (-s)
      ≤ (∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ ((d : ℝ)⁻¹)) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hpos hgm (by linarith)
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.finsetProd_rpow _ _ (fun i _ => Real.rpow_nonneg (by positivity) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  field_simp

end Sufficiency

section Necessity

/-- The cube of half-side `N` inside the lattice. -/
def latticeCube (d : ℕ) (N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem card_latticeCube (d N : ℕ) : (latticeCube d N).card = (2 * N + 1) ^ d := by
  rw [latticeCube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  omega

theorem latticeCube_subset {d : ℕ} {M N : ℕ} (h : M ≤ N) :
    latticeCube d M ⊆ latticeCube d N := by
  intro ν hν
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have hmem := Fintype.mem_piFinset.mp hν i
  rw [Finset.mem_Icc] at hmem ⊢
  have hMN : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem latticeBracket_le_of_mem_cube {d N : ℕ} {ν : Fin d → ℤ} (hν : ν ∈ latticeCube d N) :
    latticeBracket ν ≤ 1 + (d : ℝ) * (N : ℝ) := by
  rw [latticeBracket, latticeEll1]
  have hbound : ∀ i : Fin d, |((ν i : ℤ) : ℝ)| ≤ (N : ℝ) := by
    intro i
    have hmem := Fintype.mem_piFinset.mp hν i
    rw [Finset.mem_Icc] at hmem
    rw [abs_le]
    constructor
    · exact_mod_cast hmem.1
    · exact_mod_cast hmem.2
  have hsum : ∑ i, |((ν i : ℤ) : ℝ)| ≤ ∑ _i : Fin d, (N : ℝ) :=
    Finset.sum_le_sum fun i _ => hbound i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

private theorem three_pow_succ_le (n : ℕ) : (3 : ℕ) ^ (n + 1) + 1 ≤ 4 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
      have h3 : (3 : ℕ) ^ (m + 1) ≤ 4 ^ (m + 1) := Nat.pow_le_pow_left (by omega) _
      have e1 : (3 : ℕ) ^ (m + 1 + 1) = 3 * 3 ^ (m + 1) := by ring
      have e2 : (4 : ℕ) ^ (m + 1 + 1) = 4 * 4 ^ (m + 1) := by ring
      omega

/-- Every cube annulus carries at least `N^d` lattice points. -/
theorem card_annulus_ge {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    N ^ d ≤ (latticeCube d (2 * N) \ latticeCube d N).card := by
  have hsub : latticeCube d N ⊆ latticeCube d (2 * N) := latticeCube_subset (by omega)
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [card_latticeCube, card_latticeCube] at hcard
  have h1 : (4 * N) ^ d ≤ (2 * (2 * N) + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : (2 * N + 1) ^ d ≤ (3 * N) ^ d := Nat.pow_le_pow_left (by omega) d
  have hpow : (3 : ℕ) ^ d + 1 ≤ 4 ^ d := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    exact three_pow_succ_le n
  have h3 : (3 * N) ^ d + N ^ d ≤ (4 * N) ^ d := by
    have e1 : (3 * N) ^ d = 3 ^ d * N ^ d := by rw [mul_pow]
    have e2 : (4 * N) ^ d = 4 ^ d * N ^ d := by rw [mul_pow]
    rw [e1, e2]
    calc 3 ^ d * N ^ d + N ^ d = (3 ^ d + 1) * N ^ d := by ring
      _ ≤ 4 ^ d * N ^ d := Nat.mul_le_mul_right _ hpow
  omega

/-- **Necessity.**  At or below the dimension the radial polynomial lattice weight is not
summable: every cube annulus carries a fixed amount of mass. -/
theorem not_summable_latticeBracket_rpow {d : ℕ} (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ (d : ℝ)) :
    ¬ Summable (fun ν : Fin d → ℤ => latticeBracket ν ^ (-s)) := by
  intro hsum
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnn : ∀ ν : Fin d → ℤ, 0 ≤ latticeBracket ν ^ (-s) :=
    fun ν => Real.rpow_nonneg (latticeBracket_pos ν).le _
  set S : ℝ := ∑' ν : Fin d → ℤ, latticeBracket ν ^ (-s) with hSdef
  set c : ℝ := (4 * (d : ℝ)) ^ (-s) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  -- every annulus carries at least `c`
  have hannulus : ∀ N : ℕ, 1 ≤ N →
      c ≤ ∑ ν ∈ latticeCube d (2 * N) \ latticeCube d N, latticeBracket ν ^ (-s) := by
    intro N hN
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hterm : ∀ ν ∈ latticeCube d (2 * N) \ latticeCube d N,
        (4 * (d : ℝ) * (N : ℝ)) ^ (-s) ≤ latticeBracket ν ^ (-s) := by
      intro ν hν
      have hνcube : ν ∈ latticeCube d (2 * N) := (Finset.mem_sdiff.mp hν).1
      have hle := latticeBracket_le_of_mem_cube hνcube
      have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
      rw [hcast] at hle
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      refine Real.rpow_le_rpow_of_nonpos (latticeBracket_pos ν) ?_ (by linarith)
      nlinarith [hle, hd1, hNR]
    have hcount : ((N : ℝ) ^ d) * (4 * (d : ℝ) * (N : ℝ)) ^ (-s)
        ≤ ∑ ν ∈ latticeCube d (2 * N) \ latticeCube d N, latticeBracket ν ^ (-s) := by
      calc ((N : ℝ) ^ d) * (4 * (d : ℝ) * (N : ℝ)) ^ (-s)
          ≤ ((latticeCube d (2 * N) \ latticeCube d N).card : ℝ)
              * (4 * (d : ℝ) * (N : ℝ)) ^ (-s) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
            exact_mod_cast card_annulus_ge hd hN
        _ = ∑ _ν ∈ latticeCube d (2 * N) \ latticeCube d N,
              (4 * (d : ℝ) * (N : ℝ)) ^ (-s) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hterm
    refine le_trans ?_ hcount
    have hsplit : (4 * (d : ℝ) * (N : ℝ)) ^ (-s)
        = (4 * (d : ℝ)) ^ (-s) * ((N : ℝ) ^ (-s)) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
    have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ ((d : ℝ) - s) :=
      Real.one_le_rpow hNR (by linarith)
    have hNd : ((N : ℝ) ^ d) * ((N : ℝ) ^ (-s)) = (N : ℝ) ^ ((d : ℝ) - s) := by
      rw [← Real.rpow_natCast (N : ℝ) d, ← Real.rpow_add (by linarith)]
      congr 1
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * (N : ℝ) ^ ((d : ℝ) - s) := by
          exact mul_le_mul_of_nonneg_left hNpow hc.le
      _ = ((N : ℝ) ^ d) * ((4 * (d : ℝ)) ^ (-s) * ((N : ℝ) ^ (-s))) := by
          rw [hcdef, ← hNd]
          ring
      _ = ((N : ℝ) ^ d) * (4 * (d : ℝ) * (N : ℝ)) ^ (-s) := by rw [hsplit]
  -- iterate the annuli inside nested cubes
  have hgrow : ∀ K : ℕ, (K : ℝ) * c ≤ ∑ ν ∈ latticeCube d (2 ^ (K + 1)),
      latticeBracket ν ^ (-s) := by
    intro K
    induction K with
    | zero =>
        simp only [Nat.cast_zero, zero_mul]
        exact Finset.sum_nonneg fun ν _ => hnn ν
    | succ K ih =>
        have hpow : 1 ≤ 2 ^ (K + 1) := Nat.one_le_two_pow
        have hsub : latticeCube d (2 ^ (K + 1)) ⊆ latticeCube d (2 * 2 ^ (K + 1)) :=
          latticeCube_subset (by omega)
        have hsd := Finset.sum_sdiff (f := fun ν : Fin d → ℤ => latticeBracket ν ^ (-s)) hsub
        have hcube : (2 : ℕ) * 2 ^ (K + 1) = 2 ^ (K + 1 + 1) := by ring
        rw [hcube] at hsd
        have hann := hannulus (2 ^ (K + 1)) hpow
        rw [hcube] at hann
        have : ((K : ℝ) + 1) * c ≤ ∑ ν ∈ latticeCube d (2 ^ (K + 1 + 1)),
            latticeBracket ν ^ (-s) := by
          rw [← hsd]
          have := ih
          nlinarith [hann, ih]
        simpa using this
  -- but every finite partial sum is bounded by the total
  have hbdd : ∀ K : ℕ, (K : ℝ) * c ≤ S := by
    intro K
    refine le_trans (hgrow K) ?_
    exact hsum.sum_le_tsum _ (fun ν _ => hnn ν)
  obtain ⟨K, hK⟩ := exists_nat_gt (S / c)
  have := hbdd K
  rw [div_lt_iff₀ hc] at hK
  linarith

/-- **The exact summability threshold of the radial polynomial lattice weight.** -/
theorem summable_latticeBracket_rpow_iff {d : ℕ} (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s) :
    Summable (fun ν : Fin d → ℤ => latticeBracket ν ^ (-s)) ↔ (d : ℝ) < s := by
  constructor
  · intro hsum
    by_contra hcon
    exact not_summable_latticeBracket_rpow hd hs0 (not_lt.mp hcon) hsum
  · exact summable_latticeBracket_rpow hd

end Necessity

end GaloisForLFunctions.HTGeometry
