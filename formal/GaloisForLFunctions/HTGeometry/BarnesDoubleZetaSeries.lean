import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The Barnes double zeta series of a real two-dimensional cone

For `ω₁, ω₂ > 0` the Barnes double zeta is

```text
ζ₂(s, z) = ∑_{m,n ≥ 0} (z + m ω₁ + n ω₂)^{-s},
```

the Dirichlet series of the cone `ℕ ω₁ + ℕ ω₂`.  This module builds the series and proves the two
facts that carry the double-sine functional equations.

* **Convergence.**  `summable_barnesLattice_rpow`: the real cone `p`-series converges for exponent
  above two, because `c + δ(m+n) ≥ e √((1+m)(1+n))` makes the terms dominated by a product of two
  one-dimensional `p`-series of exponent `σ/2 > 1`.  `norm_cpow_neg_le_rpow` transfers this to the
  complex series with a uniform `exp(π|Im s|)` factor from the argument.

* **The shift identities.**  `barnesDoubleZeta_add_fst` and `barnesDoubleZeta_add_snd`:

  ```text
  ζ₂(s, z + ω₁) = ζ₂(s, z) - ζ₁(s, z | ω₂),
  ζ₂(s, z + ω₂) = ζ₂(s, z) - ζ₁(s, z | ω₁).
  ```

  Translating by a generator deletes one slab of the cone, which is the opposite ray.  This is pure
  reindexing: the identity is exact in the half-plane of convergence, so it propagates to every
  analytic continuation, and after regularization it becomes the double-sine step equation.

* **The ray decomposition.**  `barnesDoubleZeta_eq_tsum_rays` slices the cone into the rays
  `ℕ ω₁` translated by `ℕ ω₂`; `barnesSingleZeta_add` is the one-dimensional shift, and
  `barnesDoubleZeta_add_fst_add_snd` checks that the two period shifts commute, the initial term
  being restored after both boundary rays are removed.

Everything here is unconditional and uses only the standard axioms.
-/

open Complex Real
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The cone of the Barnes double zeta -/

/-- The lattice point `m ω₁ + n ω₂` of the two-dimensional cone. -/
def barnesLattice (o1 o2 : ℝ) (p : ℕ × ℕ) : ℝ := p.1 * o1 + p.2 * o2

theorem barnesLattice_nonneg {o1 o2 : ℝ} (h1 : 0 ≤ o1) (h2 : 0 ≤ o2) (p : ℕ × ℕ) :
    0 ≤ barnesLattice o1 o2 p :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _) h1) (mul_nonneg (Nat.cast_nonneg _) h2)

theorem barnesLattice_succ_fst (o1 o2 : ℝ) (p : ℕ × ℕ) :
    barnesLattice o1 o2 (p.1 + 1, p.2) = o1 + barnesLattice o1 o2 p := by
  simp only [barnesLattice]
  push_cast
  ring

theorem barnesLattice_succ_snd (o1 o2 : ℝ) (p : ℕ × ℕ) :
    barnesLattice o1 o2 (p.1, p.2 + 1) = o2 + barnesLattice o1 o2 p := by
  simp only [barnesLattice]
  push_cast
  ring

/-! ## Summability of the cone `p`-series -/

theorem summable_one_add_nat_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun m : ℕ => ((1 + m : ℝ)) ^ (-σ)) := by
  have hbase : Summable (fun n : ℕ => (((n : ℝ) ^ σ)⁻¹)) := summable_nat_rpow_inv.mpr hσ
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ) ^ σ)⁻¹)) 1).mpr hbase
  refine hshift.congr fun m => ?_
  rw [Real.rpow_neg (by positivity)]
  congr 2
  push_cast
  ring

/-- **The two-dimensional cone `p`-series converges for exponent above two.** -/
theorem summable_barnesLattice_rpow {o1 o2 c σ : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hc : 0 < c) (hσ : 2 < σ) :
    Summable (fun p : ℕ × ℕ => (c + barnesLattice o1 o2 p) ^ (-σ)) := by
  set δ : ℝ := min o1 o2 with hδdef
  have hδ : 0 < δ := lt_min h1 h2
  set e : ℝ := min c δ with hedef
  have he : 0 < e := lt_min hc hδ
  have hσ2 : 1 < σ / 2 := by linarith
  have hmaj : Summable (fun p : ℕ × ℕ =>
      (e ^ (-σ) * ((1 + p.1 : ℝ)) ^ (-(σ / 2))) * ((1 + p.2 : ℝ)) ^ (-(σ / 2))) :=
    Summable.mul_of_nonneg ((summable_one_add_nat_rpow_neg hσ2).mul_left (e ^ (-σ)))
      (summable_one_add_nat_rpow_neg hσ2)
      (fun m => by positivity) (fun n => by positivity)
  refine hmaj.of_nonneg_of_le (fun p => Real.rpow_nonneg (by
    have hnn := barnesLattice_nonneg h1.le h2.le p
    linarith) _) fun p => ?_
  have hpos : 0 < c + barnesLattice o1 o2 p :=
    lt_of_lt_of_le hc (le_add_of_nonneg_right (barnesLattice_nonneg h1.le h2.le p))
  have hlow : e * ((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ c + barnesLattice o1 o2 p := by
    have hsq : ((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ 1 + p.1 + p.2 := by
      have hprod : ((1 + p.1 : ℝ)) * ((1 + p.2 : ℝ)) ≤ (1 + p.1 + p.2) ^ 2 := by
        have h1' : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
        have h2' : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
        nlinarith
      have := Real.rpow_le_rpow (by positivity) hprod (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
      rw [Real.mul_rpow (by positivity) (by positivity)] at this
      calc ((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ ((1 + p.1 + p.2 : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := this
        _ = 1 + p.1 + p.2 := by
            rw [← Real.rpow_natCast (1 + (p.1 : ℝ) + p.2) 2, ← Real.rpow_mul (by positivity)]
            norm_num
    have hcone : e * (1 + p.1 + p.2) ≤ c + barnesLattice o1 o2 p := by
      have hc' : e ≤ c := min_le_left _ _
      have hd1 : e ≤ o1 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hd2 : e ≤ o2 := le_trans (min_le_right _ _) (min_le_right _ _)
      have h1' : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
      have h2' : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
      simp only [barnesLattice]
      nlinarith
    calc e * ((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2)
        = e * (((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ e * (1 + p.1 + p.2) := by
          exact mul_le_mul_of_nonneg_left hsq he.le
      _ ≤ c + barnesLattice o1 o2 p := hcone
  have hlowpos : 0 < e * ((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    positivity
  have hstep := Real.rpow_le_rpow_of_nonpos hlowpos hlow (by linarith : -σ ≤ 0)
  calc (c + barnesLattice o1 o2 p) ^ (-σ)
      ≤ (e * ((1 + p.1 : ℝ)) ^ ((1 : ℝ) / 2) * ((1 + p.2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (-σ) := hstep
    _ = e ^ (-σ) * ((1 + p.1 : ℝ)) ^ (-(σ / 2)) * ((1 + p.2 : ℝ)) ^ (-(σ / 2)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
        ring_nf


theorem summable_lattice1_rpow {o c σ : ℝ} (ho : 0 < o) (hc : 0 < c) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (c + n * o) ^ (-σ)) := by
  set e : ℝ := min c o with hedef
  have he : 0 < e := lt_min hc ho
  have hmaj : Summable (fun n : ℕ => e ^ (-σ) * ((1 + n : ℝ)) ^ (-σ)) :=
    (summable_one_add_nat_rpow_neg hσ).mul_left _
  refine hmaj.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _) fun n => ?_
  have hlow : e * (1 + n : ℝ) ≤ c + n * o := by
    have hc' : e ≤ c := min_le_left _ _
    have ho' : e ≤ o := min_le_right _ _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hlowpos : (0 : ℝ) < e * (1 + n : ℝ) := by positivity
  calc (c + n * o) ^ (-σ) ≤ (e * (1 + n : ℝ)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hlowpos hlow (by linarith)
    _ = e ^ (-σ) * ((1 + n : ℝ)) ^ (-σ) := Real.mul_rpow he.le (by positivity)

/-- The uniform bound relating the complex `cpow` norm to the real cone `p`-series. -/
theorem norm_cpow_neg_le_rpow {s w : ℂ} (hs : 0 ≤ s.re) (hw : 0 < w.re) :
    ‖w ^ (-s)‖ ≤ Real.exp (Real.pi * |s.im|) * (w.re) ^ (-s.re) := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hbound := Complex.norm_cpow_le w (-s)
  have harg : -(Real.pi * |s.im|) ≤ Complex.arg w * (-s).im := by
    have h1 : |Complex.arg w * (-s).im| ≤ Real.pi * |s.im| := by
      rw [abs_mul]
      have ha : |Complex.arg w| ≤ Real.pi := Complex.abs_arg_le_pi w
      have hb : |(-s).im| = |s.im| := by simp
      rw [hb]
      exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    linarith [neg_abs_le (Complex.arg w * (-s).im), abs_nonneg (Complex.arg w * (-s).im),
      le_abs_self (Complex.arg w * (-s).im)]
  have hexp : (Real.exp (Complex.arg w * (-s).im))⁻¹ ≤ Real.exp (Real.pi * |s.im|) := by
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnorm : ‖w‖ ^ (-s).re ≤ (w.re) ^ (-s.re) := by
    have hle : w.re ≤ ‖w‖ := Complex.re_le_norm w
    have : (-s).re = -s.re := by simp
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos hw hle (by linarith)
  calc ‖w ^ (-s)‖ ≤ ‖w‖ ^ (-s).re / Real.exp (Complex.arg w * (-s).im) := hbound
    _ = ‖w‖ ^ (-s).re * (Real.exp (Complex.arg w * (-s).im))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (w.re) ^ (-s.re) * Real.exp (Real.pi * |s.im|) := by
        refine mul_le_mul hnorm hexp (by positivity) (Real.rpow_nonneg hw.le _)
    _ = Real.exp (Real.pi * |s.im|) * (w.re) ^ (-s.re) := by ring

/-! ## The Barnes double zeta and its shift identities -/

/-- The Barnes double zeta function of the cone `ℕ ω₁ + ℕ ω₂`. -/
def barnesDoubleZeta (o1 o2 : ℝ) (s z : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, (z + (barnesLattice o1 o2 p : ℂ)) ^ (-s)

/-- The one-dimensional Barnes zeta of the ray `ℕ ω`. -/
def barnesSingleZeta (o : ℝ) (s z : ℂ) : ℂ :=
  ∑' n : ℕ, (z + ((n : ℝ) * o : ℝ)) ^ (-s)

theorem summable_barnesDoubleZeta_term {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s z : ℂ} (hs : 2 < s.re) (hz : 0 < z.re) :
    Summable (fun p : ℕ × ℕ => (z + (barnesLattice o1 o2 p : ℂ)) ^ (-s)) := by
  refine Summable.of_norm ?_
  have hmaj := (summable_barnesLattice_rpow h1 h2 hz hs).mul_left
    (Real.exp (Real.pi * |s.im|))
  refine hmaj.of_nonneg_of_le (fun p => norm_nonneg _) fun p => ?_
  have hre : (z + (barnesLattice o1 o2 p : ℂ)).re = z.re + barnesLattice o1 o2 p := by simp
  have hpos : 0 < (z + (barnesLattice o1 o2 p : ℂ)).re := by
    rw [hre]
    linarith [barnesLattice_nonneg h1.le h2.le p]
  have hb := norm_cpow_neg_le_rpow (s := s) (w := z + (barnesLattice o1 o2 p : ℂ))
    (by linarith) hpos
  rwa [hre] at hb

theorem summable_barnesSingleZeta_term {o : ℝ} (ho : 0 < o)
    {s z : ℂ} (hs : 1 < s.re) (hz : 0 < z.re) :
    Summable (fun n : ℕ => (z + ((n : ℝ) * o : ℝ)) ^ (-s)) := by
  refine Summable.of_norm ?_
  have hmaj := (summable_lattice1_rpow ho hz hs).mul_left (Real.exp (Real.pi * |s.im|))
  refine hmaj.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
  have hre : (z + ((n : ℝ) * o : ℝ)).re = z.re + n * o := by simp
  have hpos : 0 < (z + ((n : ℝ) * o : ℝ)).re := by
    rw [hre]
    have : (0 : ℝ) ≤ n * o := mul_nonneg (Nat.cast_nonneg _) ho.le
    linarith
  have hb := norm_cpow_neg_le_rpow (s := s) (w := z + ((n : ℝ) * o : ℝ)) (by linarith) hpos
  rwa [hre] at hb

/-- **The first shift identity.**  Translating the argument by `ω₁` deletes the `m = 0` slab of the
cone, which is the ray `ℕ ω₂`.  This is the exact telescoping identity behind the double-sine
functional equation. -/
theorem barnesDoubleZeta_add_fst {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s z : ℂ} (hs : 2 < s.re) (hz : 0 < z.re) :
    barnesDoubleZeta o1 o2 s (z + (o1 : ℂ))
      = barnesDoubleZeta o1 o2 s z - barnesSingleZeta o2 s z := by
  set f : ℕ × ℕ → ℂ := fun p => (z + (barnesLattice o1 o2 p : ℂ)) ^ (-s) with hf
  have hsum : Summable f := summable_barnesDoubleZeta_term h1 h2 hs hz
  have houter : Summable (fun m : ℕ => ∑' n : ℕ, f (m, n)) :=
    (hsum.hasSum.prod_fiberwise fun m => (hsum.prod_factor m).hasSum).summable
  have hsplit : barnesDoubleZeta o1 o2 s z
      = (∑' n : ℕ, f (0, n)) + ∑' m : ℕ, ∑' n : ℕ, f (m + 1, n) := by
    rw [barnesDoubleZeta, ← hf, hsum.tsum_prod, houter.tsum_eq_zero_add]
  have hzero : (∑' n : ℕ, f (0, n)) = barnesSingleZeta o2 s z := by
    rw [barnesSingleZeta]
    refine tsum_congr fun n => ?_
    have hL : barnesLattice o1 o2 (0, n) = (n : ℝ) * o2 := by
      simp [barnesLattice]
    simp only [hf]
    rw [hL]
  have hshift : (∑' m : ℕ, ∑' n : ℕ, f (m + 1, n))
      = barnesDoubleZeta o1 o2 s (z + (o1 : ℂ)) := by
    have hshiftSum : Summable (fun p : ℕ × ℕ =>
        (z + (o1 : ℂ) + (barnesLattice o1 o2 p : ℂ)) ^ (-s)) := by
      refine summable_barnesDoubleZeta_term h1 h2 hs ?_
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    rw [barnesDoubleZeta, hshiftSum.tsum_prod]
    refine tsum_congr fun m => tsum_congr fun n => ?_
    have hL : barnesLattice o1 o2 (m + 1, n) = o1 + barnesLattice o1 o2 (m, n) :=
      barnesLattice_succ_fst o1 o2 (m, n)
    simp only [hf]
    rw [hL]
    congr 1
    push_cast
    ring
  rw [← hshift, hsplit, hzero]
  ring

/-- The cone is symmetric in its two generators. -/
theorem barnesDoubleZeta_symm (o1 o2 : ℝ) (s z : ℂ) :
    barnesDoubleZeta o1 o2 s z = barnesDoubleZeta o2 o1 s z := by
  rw [barnesDoubleZeta, barnesDoubleZeta]
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq
    (fun p : ℕ × ℕ => (z + (barnesLattice o2 o1 p : ℂ)) ^ (-s))]
  refine tsum_congr fun p => ?_
  have hL : barnesLattice o2 o1 ((Equiv.prodComm ℕ ℕ) p) = barnesLattice o1 o2 p := by
    simp only [barnesLattice, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [hL]

/-- **The second shift identity.**  Translating by `ω₂` deletes the `n = 0` slab, the ray
`ℕ ω₁`. -/
theorem barnesDoubleZeta_add_snd {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s z : ℂ} (hs : 2 < s.re) (hz : 0 < z.re) :
    barnesDoubleZeta o1 o2 s (z + (o2 : ℂ))
      = barnesDoubleZeta o1 o2 s z - barnesSingleZeta o1 s z := by
  rw [barnesDoubleZeta_symm o1 o2 s (z + (o2 : ℂ)), barnesDoubleZeta_symm o1 o2 s z]
  exact barnesDoubleZeta_add_fst h2 h1 hs hz


/-! ## Ray decomposition and the commuting shifts -/

/-- **The cone is the disjoint union of its rays.**  Summing the second index first slices the
double zeta into one-dimensional zetas along `ℕ ω₁`. -/
theorem barnesDoubleZeta_eq_tsum_rays {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s z : ℂ} (hs : 2 < s.re) (hz : 0 < z.re) :
    barnesDoubleZeta o1 o2 s z = ∑' n : ℕ, barnesSingleZeta o1 s (z + ((n : ℝ) * o2 : ℝ)) := by
  set f : ℕ × ℕ → ℂ := fun p => (z + (barnesLattice o1 o2 p : ℂ)) ^ (-s) with hf
  have hsum : Summable f := summable_barnesDoubleZeta_term h1 h2 hs hz
  have hswap : Summable (fun p : ℕ × ℕ => f p.swap) := hsum.prod_symm
  rw [barnesDoubleZeta, ← hf, ← (Equiv.prodComm ℕ ℕ).tsum_eq f]
  simp only [Equiv.prodComm_apply]
  rw [hswap.tsum_prod]
  refine tsum_congr fun n => ?_
  rw [barnesSingleZeta]
  refine tsum_congr fun m => ?_
  have hL : barnesLattice o1 o2 (Prod.swap (n, m)) = (n : ℝ) * o2 + (m : ℝ) * o1 := by
    simp only [barnesLattice, Prod.fst_swap, Prod.snd_swap]
    ring
  simp only [hf, hL]
  congr 1
  push_cast
  ring

/-- **The one-dimensional shift identity.**  Translating the ray zeta by its own period deletes the
initial term. -/
theorem barnesSingleZeta_add {o : ℝ} (ho : 0 < o) {s z : ℂ} (hs : 1 < s.re) (hz : 0 < z.re) :
    barnesSingleZeta o s (z + (o : ℂ)) = barnesSingleZeta o s z - z ^ (-s) := by
  have hsum : Summable (fun n : ℕ => (z + ((n : ℝ) * o : ℝ)) ^ (-s)) :=
    summable_barnesSingleZeta_term ho hs hz
  have hsplit : barnesSingleZeta o s z
      = (z + ((0 : ℝ) * o : ℝ)) ^ (-s) + ∑' n : ℕ, (z + (((n + 1 : ℕ) : ℝ) * o : ℝ)) ^ (-s) := by
    rw [barnesSingleZeta, hsum.tsum_eq_zero_add]
    norm_num
  have hzero : (z + ((0 : ℝ) * o : ℝ)) ^ (-s) = z ^ (-s) := by norm_num
  have hshift : (∑' n : ℕ, (z + (((n + 1 : ℕ) : ℝ) * o : ℝ)) ^ (-s))
      = barnesSingleZeta o s (z + (o : ℂ)) := by
    rw [barnesSingleZeta]
    refine tsum_congr fun n => ?_
    congr 1
    push_cast
    ring
  rw [← hshift, hsplit, hzero]
  ring

/-- **The two shifts commute.**  Applying both period shifts to the double zeta removes both
boundary rays and restores the initial term counted twice. -/
theorem barnesDoubleZeta_add_fst_add_snd {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {s z : ℂ} (hs : 2 < s.re) (hz : 0 < z.re) :
    barnesDoubleZeta o1 o2 s (z + (o1 : ℂ) + (o2 : ℂ))
      = barnesDoubleZeta o1 o2 s z - barnesSingleZeta o2 s z - barnesSingleZeta o1 s z
        + z ^ (-s) := by
  have hz1 : 0 < (z + (o1 : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hstep1 := barnesDoubleZeta_add_snd h1 h2 hs hz1
  have hstep2 := barnesDoubleZeta_add_fst h1 h2 hs hz
  have hray := barnesSingleZeta_add h1 (show (1:ℝ) < s.re by linarith) hz
  rw [hstep1, hstep2, hray]
  ring

end

end GaloisForLFunctions.HTGeometry
