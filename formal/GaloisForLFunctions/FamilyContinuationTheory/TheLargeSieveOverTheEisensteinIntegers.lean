import GaloisForLFunctions.FamilyContinuationTheory.ThePlanarLargeSieve

/-!
# The large sieve over the Eisenstein integers

The family continuation over `ℚ(√−3)` bounds the mean square of an additive polynomial
`∑_{s,d} c(s,d) e(μ d/s)` over the rows `μ ∈ ℤ[ω]`, where `e(w) = exp(2πi Tr(w/√−3))` is the
additive character of `ℂ` for which `ℤ[ω]` is self-dual and `d/s` runs over fractions of
Eisenstein integers.

* **The lattice.** `eisPoint a b = a + bω`; the lattice is closed under subtraction and
  multiplication, and a nonzero lattice point has modulus at least one.
* **Dual coordinates.** `dualFst z = Tr(z/√−3)`, `dualSnd z = Tr(ωz/√−3)`: integers exactly on the
  lattice, `Tr((m + nω) z/√−3) = m · dualFst z + n · dualSnd z`, and
  `|z|² = ξ₁² + ξ₁ξ₂ + ξ₂²`. A point at distance `≥ δ` from the lattice has a dual coordinate at
  circle distance `≥ δ/2` from the integers (`half_le_toIntDist_dual_of_sep`).
* **The sieve** (`eisenstein_largeSieve`, `eisenstein_largeSieve_symmetric`). For points of `ℂ`
  that are `δ`-separated modulo the lattice,
  `∑_μ |∑_r c_r e(μ z_r)|² ≤ (2N + 2δ⁻¹ ∑_{k≤M} 1/k)² ∑_r |c_r|²`, over the rows
  `μ = m + nω` of a box with `N` values of `m` and of `n`.
* **Fractions** (`eisenstein_farey_largeSieve`). Fractions `d/s` with `|s|² ≤ Y`, distinct modulo
  the lattice, are `1/Y`-separated: the mean square is at most
  `(2N + 2Y ∑_{k≤M} 1/k)² ∑ |c|²`, which is `≪ (Q + Y² log² Y) ∑ |c|²` on a row ball of norm `Q`.
  Reduced fractions with non-associate denominators are distinct modulo the lattice
  (`exists_eq_mul_of_fraction_sub_mem`).
-/

noncomputable section

namespace GaloisForLFunctions.FamilyContinuationTheory

open Finset
open _root_.RHTower.Sieve

theorem sqrt_three_mul_self : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem sqrt_three_pos : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)

/-! ### The lattice -/

/-- The Eisenstein integer `a + bω`, `ω = −1/2 + (√3/2) i`. -/
def eisPoint (a b : ℤ) : ℂ := ⟨a - b / 2, b * (√3 / 2)⟩

@[simp] theorem eisPoint_re (a b : ℤ) : (eisPoint a b).re = a - b / 2 := rfl

@[simp] theorem eisPoint_im (a b : ℤ) : (eisPoint a b).im = b * (√3 / 2) := rfl

theorem eisPoint_add (a b c d : ℤ) : eisPoint a b + eisPoint c d = eisPoint (a + c) (b + d) := by
  apply Complex.ext
  · simp only [Complex.add_re, eisPoint_re]; push_cast; ring
  · simp only [Complex.add_im, eisPoint_im]; push_cast; ring

theorem eisPoint_sub (a b c d : ℤ) : eisPoint a b - eisPoint c d = eisPoint (a - c) (b - d) := by
  apply Complex.ext
  · simp only [Complex.sub_re, eisPoint_re]; push_cast; ring
  · simp only [Complex.sub_im, eisPoint_im]; push_cast; ring

/-- Multiplication in the basis `1, ω`: `ω² = −1 − ω`. -/
theorem eisPoint_mul (a b c d : ℤ) :
    eisPoint a b * eisPoint c d = eisPoint (a * c - b * d) (a * d + b * c - b * d) := by
  apply Complex.ext
  · simp only [Complex.mul_re, eisPoint_re, eisPoint_im]
    push_cast
    linear_combination (-((b : ℝ) * d / 4)) * sqrt_three_mul_self
  · simp only [Complex.mul_im, eisPoint_re, eisPoint_im]
    push_cast
    ring

/-- The Eisenstein lattice `ℤ[ω]` in `ℂ`. -/
def eisLattice : Set ℂ := {z | ∃ a b : ℤ, z = eisPoint a b}

theorem eisPoint_mem (a b : ℤ) : eisPoint a b ∈ eisLattice := ⟨a, b, rfl⟩

theorem eisLattice_add_mem {z w : ℂ} (hz : z ∈ eisLattice) (hw : w ∈ eisLattice) :
    z + w ∈ eisLattice := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, eisPoint_add a b c d⟩

theorem eisLattice_sub_mem {z w : ℂ} (hz : z ∈ eisLattice) (hw : w ∈ eisLattice) :
    z - w ∈ eisLattice := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a - c, b - d, eisPoint_sub a b c d⟩

theorem eisLattice_mul_mem {z w : ℂ} (hz : z ∈ eisLattice) (hw : w ∈ eisLattice) :
    z * w ∈ eisLattice := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a * c - b * d, a * d + b * c - b * d, eisPoint_mul a b c d⟩

/-- The norm form: `|a + bω|² = a² − ab + b²`. -/
theorem norm_sq_eisPoint (a b : ℤ) :
    ‖eisPoint a b‖ ^ 2 = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, eisPoint_re, eisPoint_im]
  push_cast
  linear_combination ((b : ℝ) ^ 2 / 4) * sqrt_three_mul_self

/-- A nonzero Eisenstein integer has modulus at least one. -/
theorem one_le_norm_of_mem_eisLattice {z : ℂ} (hz : z ∈ eisLattice) (h0 : z ≠ 0) : 1 ≤ ‖z‖ := by
  obtain ⟨a, b, rfl⟩ := hz
  have hint : (1 : ℤ) ≤ a ^ 2 - a * b + b ^ 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have hb2 : b ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (2 * a - b)]) (sq_nonneg b)
    have hb : b = 0 := by simpa using hb2
    have ha2 : a ^ 2 = 0 := le_antisymm (by rw [hb] at hlt; nlinarith) (sq_nonneg a)
    have ha : a = 0 := by simpa using ha2
    apply h0
    rw [ha, hb]
    apply Complex.ext <;> simp
  have h1 : (1 : ℝ) ≤ ‖eisPoint a b‖ ^ 2 := by
    rw [norm_sq_eisPoint]
    exact_mod_cast hint
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg (eisPoint a b)]

/-- A row of norm at most `Q` lies in the box `m², n² ≤ 4Q/3`. -/
theorem sq_le_of_norm_sq_eisPoint_le {m n : ℤ} {Q : ℝ} (h : ‖eisPoint m n‖ ^ 2 ≤ Q) :
    (m : ℝ) ^ 2 ≤ 4 * Q / 3 ∧ (n : ℝ) ^ 2 ≤ 4 * Q / 3 := by
  rw [norm_sq_eisPoint] at h
  push_cast at h
  constructor
  · nlinarith [sq_nonneg ((m : ℝ) - 2 * n)]
  · nlinarith [sq_nonneg (2 * (m : ℝ) - n)]

/-! ### Dual coordinates -/

/-- `Tr(z/√−3) = (2/√3) Im z`. -/
def dualFst (z : ℂ) : ℝ := 2 / √3 * z.im

/-- `Tr(ωz/√−3) = Re z − Im z/√3`. -/
def dualSnd (z : ℂ) : ℝ := z.re - z.im / √3

theorem dualFst_add (z w : ℂ) : dualFst (z + w) = dualFst z + dualFst w := by
  simp only [dualFst, Complex.add_im]; ring

theorem dualSnd_add (z w : ℂ) : dualSnd (z + w) = dualSnd z + dualSnd w := by
  simp only [dualSnd, Complex.add_re, Complex.add_im]; ring

theorem dualFst_sub (z w : ℂ) : dualFst (z - w) = dualFst z - dualFst w := by
  simp only [dualFst, Complex.sub_im]; ring

theorem dualSnd_sub (z w : ℂ) : dualSnd (z - w) = dualSnd z - dualSnd w := by
  simp only [dualSnd, Complex.sub_re, Complex.sub_im]; ring

theorem dualFst_eisPoint (a b : ℤ) : dualFst (eisPoint a b) = b := by
  have h := sqrt_three_pos.ne'
  simp only [dualFst, eisPoint_im]
  field_simp

theorem dualSnd_eisPoint (a b : ℤ) : dualSnd (eisPoint a b) = a - b := by
  have h := sqrt_three_pos.ne'
  simp only [dualSnd, eisPoint_re, eisPoint_im]
  field_simp
  ring

/-- The trace pairing with a lattice point in dual coordinates. -/
theorem dualFst_eisPoint_mul (m n : ℤ) (z : ℂ) :
    dualFst (eisPoint m n * z) = m * dualFst z + n * dualSnd z := by
  have h := sqrt_three_pos.ne'
  simp only [dualFst, dualSnd, Complex.mul_im, eisPoint_re, eisPoint_im]
  field_simp
  ring

/-- The modulus in dual coordinates: `|z|² = ξ₁² + ξ₁ξ₂ + ξ₂²`. -/
theorem norm_sq_eq_dual (z : ℂ) :
    ‖z‖ ^ 2 = dualFst z ^ 2 + dualFst z * dualSnd z + dualSnd z ^ 2 := by
  have h := sqrt_three_pos.ne'
  obtain ⟨u, him⟩ : ∃ u : ℝ, z.im = u * √3 := ⟨z.im / √3, by field_simp⟩
  have h1 : dualFst z = 2 * u := by rw [dualFst, him]; field_simp
  have h2 : dualSnd z = z.re - u := by rw [dualSnd, him]; field_simp
  rw [Complex.sq_norm, Complex.normSq_apply, h1, h2, him]
  linear_combination u ^ 2 * sqrt_three_mul_self

/-- A point whose dual coordinates are both within `δ` of the integers is within `√3 δ` of the
lattice. -/
theorem exists_mem_eisLattice_norm_sub_lt {w : ℂ} {δ : ℝ}
    (h₁ : toIntDist (dualFst w) < δ) (h₂ : toIntDist (dualSnd w) < δ) :
    ∃ n ∈ eisLattice, ‖w - n‖ ^ 2 < 3 * δ ^ 2 := by
  refine ⟨eisPoint (round (dualSnd w) + round (dualFst w)) (round (dualFst w)),
    eisPoint_mem _ _, ?_⟩
  have hkey : ‖w - eisPoint (round (dualSnd w) + round (dualFst w)) (round (dualFst w))‖ ^ 2
      = (dualFst w - round (dualFst w)) ^ 2
        + (dualFst w - round (dualFst w)) * (dualSnd w - round (dualSnd w))
        + (dualSnd w - round (dualSnd w)) ^ 2 := by
    rw [norm_sq_eq_dual, dualFst_sub, dualSnd_sub, dualFst_eisPoint, dualSnd_eisPoint]
    push_cast
    ring
  rw [hkey]
  obtain ⟨a1, a2⟩ := abs_lt.mp (show |dualFst w - round (dualFst w)| < δ from h₁)
  obtain ⟨b1, b2⟩ := abs_lt.mp (show |dualSnd w - round (dualSnd w)| < δ from h₂)
  nlinarith [mul_pos (sub_pos.2 a2) (sub_pos.2 (neg_lt.1 a1) : 0 < δ - -(dualFst w - round (dualFst w))),
    mul_pos (sub_pos.2 b2) (sub_pos.2 (neg_lt.1 b1) : 0 < δ - -(dualSnd w - round (dualSnd w))),
    mul_pos (sub_pos.2 a2) (sub_pos.2 (neg_lt.1 b1) : 0 < δ - -(dualSnd w - round (dualSnd w))),
    mul_pos (sub_pos.2 b2) (sub_pos.2 (neg_lt.1 a1) : 0 < δ - -(dualFst w - round (dualFst w)))]

/-- **Separation in dual coordinates.** A point at distance at least `δ` from every lattice point
has a dual coordinate at circle distance at least `δ/2` from the integers. -/
theorem half_le_toIntDist_dual_of_sep {w : ℂ} {δ : ℝ} (hδ0 : 0 < δ)
    (hw : ∀ n ∈ eisLattice, δ ≤ ‖w - n‖) :
    δ / 2 ≤ toIntDist (dualFst w) ∨ δ / 2 ≤ toIntDist (dualSnd w) := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨n, hn, hlt⟩ := exists_mem_eisLattice_norm_sub_lt hcon.1 hcon.2
  have hge := hw n hn
  nlinarith [mul_nonneg (sub_nonneg.2 hge) (add_nonneg (norm_nonneg (w - n)) hδ0.le)]

/-! ### The additive character -/

theorem circleFreq_add (a b : ℝ) : circleFreq (a + b) = circleFreq a * circleFreq b := by
  rw [circleFreq, circleFreq, circleFreq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem circleFreq_nat_mul (k : ℕ) (a : ℝ) : circleFreq (k * a) = circleFreq a ^ k := by
  rw [circleFreq, circleFreq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The additive character `e(w) = exp(2πi Tr(w/√−3))` of `ℂ`. -/
def eisChar (w : ℂ) : ℂ := circleFreq (dualFst w)

theorem norm_eisChar (w : ℂ) : ‖eisChar w‖ = 1 := norm_circleFreq _

theorem eisChar_add (w w' : ℂ) : eisChar (w + w') = eisChar w * eisChar w' := by
  rw [eisChar, dualFst_add, circleFreq_add, eisChar, eisChar]

/-- On a row `m + nω` with `m, n ≥ 0` the character is a monomial in two circle frequencies. -/
theorem eisChar_eisPoint_mul (m n : ℕ) (z : ℂ) :
    eisChar (eisPoint m n * z) = circleFreq (dualFst z) ^ m * circleFreq (dualSnd z) ^ n := by
  rw [eisChar, dualFst_eisPoint_mul, circleFreq_add]
  push_cast
  rw [circleFreq_nat_mul, circleFreq_nat_mul]

/-! ### The sieve -/

/-- **The large sieve over the Eisenstein integers.** Points of `ℂ` that are `δ`-separated
modulo the lattice, rows `m + nω` with `0 ≤ m, n < N`. -/
theorem eisenstein_largeSieve {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (z : ι → ℂ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ n ∈ eisLattice, δ ≤ ‖z b - z a - n‖)
    {M : ℕ} (hM : 1 / δ ≤ (M : ℝ)) (c : ι → ℂ) :
    ∑ μ : Fin N × Fin N,
        ‖∑ r ∈ s, c r * eisChar (eisPoint (μ.1 : ℕ) (μ.2 : ℕ) * z r)‖ ^ (2 : ℕ)
      ≤ (2 * N + 2 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) := by
  have hM' : 1 / (2 * (δ / 2)) ≤ (M : ℝ) := by
    have : 1 / (2 * (δ / 2)) = 1 / δ := by field_simp
    rw [this]; exact hM
  have h := sum_norm_sq_sum_mul_le N s (fun r => dualFst (z r)) (fun r => dualSnd (z r))
    (δ := δ / 2) (by positivity) (by linarith)
    (fun a ha b hb hab => by
      have := half_le_toIntDist_dual_of_sep hδ0 (hsep a ha b hb hab)
      rwa [dualFst_sub, dualSnd_sub] at this) hM' c
  rw [one_div_div] at h
  simpa only [eisChar_eisPoint_mul] using h

/-- Reindexing a symmetric interval of integers. -/
theorem sum_Icc_neg_eq_sum_range (K : ℕ) (g : ℤ → ℝ) :
    ∑ m ∈ Icc (-(K : ℤ)) K, g m = ∑ i ∈ range (2 * K + 1), g ((i : ℤ) - K) := by
  refine Finset.sum_nbij' (fun m => (m + K).toNat) (fun i => (i : ℤ) - K) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_Icc] at hm
    rw [mem_range]
    omega
  · intro i hi
    rw [mem_range] at hi
    rw [mem_Icc]
    omega
  · intro m hm
    rw [mem_Icc] at hm
    omega
  · intro i _
    omega
  · intro m hm
    rw [mem_Icc] at hm
    congr 1
    omega

/-- **The sieve on a symmetric box of rows**, `μ = m + nω` with `|m|, |n| ≤ K`; the box contains
the ball of norm `3K²/4` (`sq_le_of_norm_sq_eisPoint_le`). -/
theorem eisenstein_largeSieve_symmetric {ι : Type*} [DecidableEq ι] (K : ℕ) (s : Finset ι)
    (z : ι → ℂ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ n ∈ eisLattice, δ ≤ ‖z b - z a - n‖)
    {M : ℕ} (hM : 1 / δ ≤ (M : ℝ)) (c : ι → ℂ) :
    ∑ m ∈ Icc (-(K : ℤ)) K, ∑ n ∈ Icc (-(K : ℤ)) K,
        ‖∑ r ∈ s, c r * eisChar (eisPoint m n * z r)‖ ^ (2 : ℕ)
      ≤ (2 * (2 * K + 1 : ℕ) + 2 / δ * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2
          * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) := by
  -- shift the rows into the positive box; the shift is a unimodular factor of the coefficients
  have h := eisenstein_largeSieve (2 * K + 1) s z hδ0 hδ hsep hM
    (fun r => c r * eisChar (eisPoint (-(K : ℤ)) (-(K : ℤ)) * z r))
  have hnorm : ∑ r ∈ s, ‖c r * eisChar (eisPoint (-(K : ℤ)) (-(K : ℤ)) * z r)‖ ^ (2 : ℕ)
      = ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) :=
    Finset.sum_congr rfl fun r _ => by rw [norm_mul, norm_eisChar, mul_one]
  rw [hnorm] at h
  refine le_trans (le_of_eq ?_) h
  have hshift : ∀ (i j : ℕ) (r : ι),
      c r * eisChar (eisPoint (-(K : ℤ)) (-(K : ℤ)) * z r) * eisChar (eisPoint i j * z r)
        = c r * eisChar (eisPoint ((i : ℤ) - K) ((j : ℤ) - K) * z r) := by
    intro i j r
    rw [mul_assoc, ← eisChar_add, ← add_mul, eisPoint_add]
    congr 4 <;> ring
  rw [Fintype.sum_prod_type, sum_Icc_neg_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range
      (fun i => ∑ n ∈ Icc (-(K : ℤ)) K,
        ‖∑ r ∈ s, c r * eisChar (eisPoint ((i : ℤ) - K) n * z r)‖ ^ (2 : ℕ)) (2 * K + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Icc_neg_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range
      (fun j => ‖∑ r ∈ s, c r * eisChar (eisPoint ((i : ℕ) - K) ((j : ℤ) - K) * z r)‖ ^ (2 : ℕ))
      (2 * K + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun r _ => (hshift i j r).symm

/-! ### Fractions -/

/-- **Separation of fractions.** Two fractions of Eisenstein integers that differ by a
non-integer are at distance at least `1/(|s||s'|)` modulo the lattice. -/
theorem one_div_le_norm_fraction_sub {d s d' s' n : ℂ} (hd : d ∈ eisLattice)
    (hs : s ∈ eisLattice) (hd' : d' ∈ eisLattice) (hs' : s' ∈ eisLattice) (hn : n ∈ eisLattice)
    (hs0 : s ≠ 0) (hs0' : s' ≠ 0) (hne : d / s - d' / s' ∉ eisLattice) :
    1 / (‖s‖ * ‖s'‖) ≤ ‖d / s - d' / s' - n‖ := by
  have hw : d * s' - d' * s - n * (s * s') ∈ eisLattice :=
    eisLattice_sub_mem (eisLattice_sub_mem (eisLattice_mul_mem hd hs') (eisLattice_mul_mem hd' hs))
      (eisLattice_mul_mem hn (eisLattice_mul_mem hs hs'))
  have hw0 : d * s' - d' * s - n * (s * s') ≠ 0 := by
    intro h0
    apply hne
    have : d / s - d' / s' = n := by
      field_simp
      linear_combination h0
    rw [this]
    exact hn
  have heq : d / s - d' / s' - n = (d * s' - d' * s - n * (s * s')) / (s * s') := by
    field_simp
  rw [heq, norm_div, norm_mul]
  have hpos : 0 < ‖s‖ * ‖s'‖ := mul_pos (norm_pos_iff.2 hs0) (norm_pos_iff.2 hs0')
  exact div_le_div_of_nonneg_right (one_le_norm_of_mem_eisLattice hw hw0) hpos.le

/-- **Reduced fractions.** If `d/s − d'/s'` is an Eisenstein integer and `d` is coprime to `s`,
then `s` divides `s'`. -/
theorem exists_eq_mul_of_fraction_sub_mem {d s d' s' : ℂ} (hd' : d' ∈ eisLattice)
    (hs' : s' ∈ eisLattice) (hs0 : s ≠ 0) (hs0' : s' ≠ 0)
    (hcop : ∃ u ∈ eisLattice, ∃ v ∈ eisLattice, u * d + v * s = 1)
    (h : d / s - d' / s' ∈ eisLattice) : ∃ e ∈ eisLattice, s' = e * s := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcop
  refine ⟨u * (d' + (d / s - d' / s') * s') + v * s',
    eisLattice_add_mem (eisLattice_mul_mem hu
      (eisLattice_add_mem hd' (eisLattice_mul_mem h hs'))) (eisLattice_mul_mem hv hs'), ?_⟩
  have hds : d * s' = s * (d' + (d / s - d' / s') * s') := by
    field_simp
    ring
  linear_combination (-s') * huv + u * hds

/-- **The large sieve for fractions of Eisenstein integers.** Pairs `(d, s)` with `|s|² ≤ Y`
whose fractions are distinct modulo the lattice; rows `m + nω` with `0 ≤ m, n < N`. -/
theorem eisenstein_farey_largeSieve (N : ℕ) (P : Finset (ℂ × ℂ)) {Y : ℝ} (hY : 1 ≤ Y)
    (hmem : ∀ p ∈ P, p.1 ∈ eisLattice ∧ p.2 ∈ eisLattice ∧ p.2 ≠ 0 ∧ ‖p.2‖ ^ 2 ≤ Y)
    (hdist : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → q.1 / q.2 - p.1 / p.2 ∉ eisLattice)
    {M : ℕ} (hM : Y ≤ (M : ℝ)) (c : ℂ × ℂ → ℂ) :
    ∑ μ : Fin N × Fin N,
        ‖∑ p ∈ P, c p * eisChar (eisPoint (μ.1 : ℕ) (μ.2 : ℕ) * (p.1 / p.2))‖ ^ (2 : ℕ)
      ≤ (2 * N + 2 * Y * ∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ^ 2 * ∑ p ∈ P, ‖c p‖ ^ (2 : ℕ) := by
  classical
  have hY0 : 0 < Y := by linarith
  have h := eisenstein_largeSieve N P (fun p => p.1 / p.2) (δ := 1 / Y) (by positivity)
    (by rw [div_le_one hY0]; exact hY)
    (fun p hp q hq hpq n hn => by
      obtain ⟨hd, hs, hs0, hsY⟩ := hmem p hp
      obtain ⟨hd', hs', hs0', hsY'⟩ := hmem q hq
      refine le_trans ?_
        (one_div_le_norm_fraction_sub hd' hs' hd hs hn hs0' hs0 (hdist p hp q hq hpq))
      have hprod : ‖q.2‖ * ‖p.2‖ ≤ Y := by nlinarith [sq_nonneg (‖q.2‖ - ‖p.2‖)]
      exact one_div_le_one_div_of_le
        (mul_pos (norm_pos_iff.2 hs0') (norm_pos_iff.2 hs0)) hprod)
    (M := M) (by rw [one_div_one_div]; exact hM) c
  have hconst : (2 : ℝ) / (1 / Y) = 2 * Y := by field_simp
  rwa [hconst] at h

end GaloisForLFunctions.FamilyContinuationTheory
