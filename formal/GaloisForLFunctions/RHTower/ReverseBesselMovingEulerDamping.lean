import GaloisForLFunctions.RHTower.ReverseBesselGammaHalfLogReserve

/-!
# Moving-degree reverse-Bessel packets recover Euler damping

Let `p(n,j) = j! b(n,j)/b(n,0)`.  The coefficient domination behind fixed-frequency blindness
only says `0 ≤ p(n,j) ≤ 1`.  The exact adjacent recurrence gives more once the jet order passes
half the degree: if `j ≥ ceil(n/2)`, then

`p(n,j+1) ≤ (2/3) p(n,j)`.

Splitting the normalized reverse-Bessel polynomial at `r = ceil(n/2)` therefore gives the finite
moving-degree bound

`R_n(x) ≤ 2^r exp(x/2) + (3/2)^r exp(2x/3)`,  `x ≥ 0`.

After multiplication by the Euler factor `exp(-x)`, one half or one third of the damping survives.
The closed specialization `x = 6N log(m+2)` is the source-scale form needed for the completed
prime packet.  This is genuinely uniform in degree and is not a consequence of the fixed-argument
limit `R_n(x) → exp x`.
-/

open scoped BigOperators
open Finset

namespace RHTower

noncomputable section

/-- Factorial-normalized reverse-Bessel coefficient. -/
def reverseBesselPoissonCoeff (n j : ℕ) : ℝ :=
  reverseBesselRatio n j * (j.factorial : ℝ)

/-- Reverse-Bessel polynomial normalized by its constant coefficient. -/
def reverseBesselNormalizedPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), reverseBesselRatio n j * x ^ j

theorem reverseBesselNormalizedPoly_eq_div (n : ℕ) (x : ℝ) :
    reverseBesselNormalizedPoly n x =
      reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ) := by
  rw [reverseBesselNormalizedPoly, reverseBesselPoly, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [reverseBesselRatio]
  ring

theorem reverseBesselPoissonCoeff_nonneg (n j : ℕ) :
    0 ≤ reverseBesselPoissonCoeff n j := by
  exact mul_nonneg (reverseBesselRatio_nonneg_all n j) (by positivity)

theorem reverseBesselPoissonCoeff_le_one (n j : ℕ) :
    reverseBesselPoissonCoeff n j ≤ 1 := by
  rw [reverseBesselPoissonCoeff]
  calc
    reverseBesselRatio n j * (j.factorial : ℝ)
        ≤ (1 / (j.factorial : ℝ)) * (j.factorial : ℝ) := by
          gcongr
          exact reverseBesselRatio_le_factorial_all n j
    _ = 1 := by field_simp

theorem reverseBesselNormalizedPoly_eq_poissonSum (n : ℕ) (x : ℝ) :
    reverseBesselNormalizedPoly n x =
      ∑ j ∈ Finset.range (n + 1),
        reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ) := by
  rw [reverseBesselNormalizedPoly]
  apply Finset.sum_congr rfl
  intro j _
  rw [reverseBesselPoissonCoeff]
  field_simp

/-- Cleared adjacent recurrence for the factorial-normalized coefficients. -/
theorem reverseBesselPoissonCoeff_succ_cleared {n j : ℕ} (hj : j < n) :
    (2 * (n : ℝ) - j) * reverseBesselPoissonCoeff n (j + 1) =
      2 * ((n : ℝ) - j) * reverseBesselPoissonCoeff n j := by
  rw [reverseBesselPoissonCoeff, reverseBesselPoissonCoeff,
    reverseBesselRatio_succ_eq (n := n) (j := j) hj, Nat.factorial_succ]
  push_cast
  have hden1 : 2 * (n : ℝ) - j ≠ 0 := by
    have hjR : (j : ℝ) < n := by exact_mod_cast hj
    nlinarith
  have hden2 : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Past half the degree, each factorial-normalized coefficient contracts by at least `2/3`. -/
theorem reverseBesselPoissonCoeff_succ_le_twoThird {n j : ℕ}
    (hhalf : n ≤ 2 * j) (hj : j < n) :
    reverseBesselPoissonCoeff n (j + 1) ≤
      (2 / 3 : ℝ) * reverseBesselPoissonCoeff n j := by
  have hrec := reverseBesselPoissonCoeff_succ_cleared (n := n) (j := j) hj
  have hden : 0 < 2 * (n : ℝ) - j := by
    have hjR : (j : ℝ) < n := by exact_mod_cast hj
    nlinarith
  have hscalar : 2 * ((n : ℝ) - j) / (2 * (n : ℝ) - j) ≤ 2 / 3 := by
    rw [div_le_iff₀ hden]
    have hhalfR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hhalf
    nlinarith
  have hnext : reverseBesselPoissonCoeff n (j + 1) =
      (2 * ((n : ℝ) - j) / (2 * (n : ℝ) - j)) *
        reverseBesselPoissonCoeff n j := by
    rw [show
      (2 * ((n : ℝ) - j) / (2 * (n : ℝ) - j)) * reverseBesselPoissonCoeff n j =
        (2 * ((n : ℝ) - j) * reverseBesselPoissonCoeff n j) /
          (2 * (n : ℝ) - j) by ring]
    rw [eq_div_iff hden.ne']
    linear_combination hrec
  rw [hnext]
  exact mul_le_mul_of_nonneg_right hscalar (reverseBesselPoissonCoeff_nonneg n j)

/-- Geometric coefficient phase after any cutoff at or beyond half degree. -/
theorem reverseBesselPoissonCoeff_le_twoThird_pow {n r k : ℕ}
    (hhalf : n ≤ 2 * r) (hrk : r + k ≤ n) :
    reverseBesselPoissonCoeff n (r + k) ≤ (2 / 3 : ℝ) ^ k := by
  induction k with
  | zero =>
      simpa using reverseBesselPoissonCoeff_le_one n r
  | succ k ih =>
      have hrk' : r + k ≤ n := by omega
      have hj : r + k < n := by omega
      have hhalf' : n ≤ 2 * (r + k) := by omega
      calc
        reverseBesselPoissonCoeff n (r + (k + 1)) =
            reverseBesselPoissonCoeff n ((r + k) + 1) := by
              rw [show r + (k + 1) = (r + k) + 1 by omega]
        _ ≤ (2 / 3 : ℝ) * reverseBesselPoissonCoeff n (r + k) :=
          reverseBesselPoissonCoeff_succ_le_twoThird hhalf' hj
        _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ k := by
          gcongr
          exact ih hrk'
        _ = (2 / 3 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

theorem sum_range_reverseBesselPoissonCoeff_le_halfExp
    (n r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ j ∈ Finset.range r,
        reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ) ≤
      (2 : ℝ) ^ r * Real.exp (x / 2) := by
  have hterm : ∀ j ∈ Finset.range r,
      reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ) ≤
        (2 : ℝ) ^ r * ((x / 2) ^ j / (j.factorial : ℝ)) := by
    intro j hj
    have hjr : j ≤ r := (Finset.mem_range.mp hj).le
    have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ r := by
      obtain ⟨k, rfl⟩ : ∃ k, r = j + k := ⟨r - j, by omega⟩
      rw [pow_add]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    have hbase : 0 ≤ (x / 2) ^ j / (j.factorial : ℝ) := by positivity
    calc
      reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ)
          ≤ 1 * x ^ j / (j.factorial : ℝ) := by
            gcongr
            exact reverseBesselPoissonCoeff_le_one n j
      _ = (2 : ℝ) ^ j * ((x / 2) ^ j / (j.factorial : ℝ)) := by
        rw [div_pow]
        field_simp
      _ ≤ (2 : ℝ) ^ r * ((x / 2) ^ j / (j.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow hbase
  calc
    ∑ j ∈ Finset.range r,
        reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ)
        ≤ ∑ j ∈ Finset.range r,
          (2 : ℝ) ^ r * ((x / 2) ^ j / (j.factorial : ℝ)) :=
            Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ r *
        ∑ j ∈ Finset.range r, (x / 2) ^ j / (j.factorial : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ r * Real.exp (x / 2) := by
      gcongr
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      exact Summable.sum_le_tsum (Finset.range r) (fun j _ => by positivity)
        (Real.summable_pow_div_factorial (x / 2))

theorem sum_Ico_reverseBesselPoissonCoeff_le_twoThirdExp
    {n r : ℕ} (hhalf : n ≤ 2 * r) {x : ℝ} (hx : 0 ≤ x) :
    ∑ j ∈ Finset.Ico r (n + 1),
        reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ) ≤
      (3 / 2 : ℝ) ^ r * Real.exp ((2 / 3 : ℝ) * x) := by
  have hterm : ∀ j ∈ Finset.Ico r (n + 1),
      reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ) ≤
        (3 / 2 : ℝ) ^ r *
          ((((2 / 3 : ℝ) * x) ^ j) / (j.factorial : ℝ)) := by
    intro j hj
    have hrj : r ≤ j := (Finset.mem_Ico.mp hj).1
    have hjlt : j < n + 1 := (Finset.mem_Ico.mp hj).2
    have hjn : j ≤ n := by omega
    have hidx : r + (j - r) = j := Nat.add_sub_of_le hrj
    have hrk : r + (j - r) ≤ n := by rw [hidx]; exact hjn
    have hp0 := reverseBesselPoissonCoeff_le_twoThird_pow
      (n := n) (r := r) (k := j - r) hhalf hrk
    have hp : reverseBesselPoissonCoeff n j ≤ (2 / 3 : ℝ) ^ (j - r) := by
      simpa [Nat.add_sub_of_le hrj] using hp0
    have hnonneg : 0 ≤ x ^ j / (j.factorial : ℝ) := by positivity
    have hscale :
        (2 / 3 : ℝ) ^ (j - r) * (x ^ j / (j.factorial : ℝ)) =
          (3 / 2 : ℝ) ^ r *
            ((((2 / 3 : ℝ) * x) ^ j) / (j.factorial : ℝ)) := by
      rw [mul_pow]
      have hqpow : (2 / 3 : ℝ) ^ j =
          (2 / 3 : ℝ) ^ (j - r) * (2 / 3 : ℝ) ^ r := by
        rw [← pow_add, Nat.sub_add_cancel hrj]
      rw [hqpow]
      have hcancel : (3 / 2 : ℝ) ^ r * (2 / 3 : ℝ) ^ r = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (2 / 3 : ℝ) ^ (j - r) * (x ^ j / (j.factorial : ℝ)) =
            1 * ((2 / 3 : ℝ) ^ (j - r) *
              (x ^ j / (j.factorial : ℝ))) := by ring
        _ = ((3 / 2 : ℝ) ^ r * (2 / 3 : ℝ) ^ r) *
            ((2 / 3 : ℝ) ^ (j - r) *
              (x ^ j / (j.factorial : ℝ))) := by rw [hcancel]
        _ = (3 / 2 : ℝ) ^ r *
            (((2 / 3 : ℝ) ^ (j - r) * (2 / 3 : ℝ) ^ r * x ^ j) /
              (j.factorial : ℝ)) := by ring
    calc
      reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ)
          = reverseBesselPoissonCoeff n j *
              (x ^ j / (j.factorial : ℝ)) := by ring
      _ ≤ (2 / 3 : ℝ) ^ (j - r) *
          (x ^ j / (j.factorial : ℝ)) := mul_le_mul_of_nonneg_right hp hnonneg
      _ = (3 / 2 : ℝ) ^ r *
          ((((2 / 3 : ℝ) * x) ^ j) / (j.factorial : ℝ)) := hscale
  calc
    ∑ j ∈ Finset.Ico r (n + 1),
        reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ)
        ≤ ∑ j ∈ Finset.Ico r (n + 1),
          (3 / 2 : ℝ) ^ r *
            ((((2 / 3 : ℝ) * x) ^ j) / (j.factorial : ℝ)) :=
              Finset.sum_le_sum hterm
    _ = (3 / 2 : ℝ) ^ r *
        ∑ j ∈ Finset.Ico r (n + 1),
          (((2 / 3 : ℝ) * x) ^ j) / (j.factorial : ℝ) := by
            rw [Finset.mul_sum]
    _ ≤ (3 / 2 : ℝ) ^ r * Real.exp ((2 / 3 : ℝ) * x) := by
      gcongr
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      exact Summable.sum_le_tsum (Finset.Ico r (n + 1)) (fun j _ => by positivity)
        (Real.summable_pow_div_factorial ((2 / 3 : ℝ) * x))

/-- Moving-degree two-rate bound for the normalized reverse-Bessel polynomial. -/
theorem reverseBesselNormalizedPoly_le_movingSplit
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    let r := (n + 1) / 2
    reverseBesselNormalizedPoly n x ≤
      (2 : ℝ) ^ r * Real.exp (x / 2) +
        (3 / 2 : ℝ) ^ r * Real.exp ((2 / 3 : ℝ) * x) := by
  let r := (n + 1) / 2
  have hhalf : n ≤ 2 * r := by dsimp [r]; omega
  have hr : r ≤ n + 1 := by dsimp [r]; omega
  have hhead := sum_range_reverseBesselPoissonCoeff_le_halfExp n r hx
  have htail := sum_Ico_reverseBesselPoissonCoeff_le_twoThirdExp
    (n := n) (r := r) hhalf hx
  rw [reverseBesselNormalizedPoly_eq_poissonSum]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j => reverseBesselPoissonCoeff n j * x ^ j / (j.factorial : ℝ)) hr
  rw [← hsplit]
  linarith

/-- Euler damping reappears at moving degree: one part retains half the damping and the other
retains one third. -/
theorem exp_neg_mul_reverseBesselNormalizedPoly_le_movingDamping
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    let r := (n + 1) / 2
    Real.exp (-x) * reverseBesselNormalizedPoly n x ≤
      (2 : ℝ) ^ r * Real.exp (-(x / 2)) +
        (3 / 2 : ℝ) ^ r * Real.exp (-(x / 3)) := by
  let r := (n + 1) / 2
  have hpoly := reverseBesselNormalizedPoly_le_movingSplit n hx
  have hexp : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hpoly hexp
  have hhalf : Real.exp (-x) * Real.exp (x / 2) = Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hthird : Real.exp (-x) * Real.exp ((2 / 3 : ℝ) * x) =
      Real.exp (-(x / 3)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp (-x) * reverseBesselNormalizedPoly n x ≤
    (2 : ℝ) ^ r * Real.exp (-(x / 2)) +
      (3 / 2 : ℝ) ^ r * Real.exp (-(x / 3))
  calc
    Real.exp (-x) * reverseBesselNormalizedPoly n x ≤
        Real.exp (-x) *
          ((2 : ℝ) ^ r * Real.exp (x / 2) +
            (3 / 2 : ℝ) ^ r * Real.exp ((2 / 3 : ℝ) * x)) := hmul
    _ = (2 : ℝ) ^ r * Real.exp (-(x / 2)) +
        (3 / 2 : ℝ) ^ r * Real.exp (-(x / 3)) := by
      rw [mul_add]
      rw [show Real.exp (-x) * ((2 : ℝ) ^ r * Real.exp (x / 2)) =
          (2 : ℝ) ^ r * (Real.exp (-x) * Real.exp (x / 2)) by ring,
        show Real.exp (-x) * ((3 / 2 : ℝ) ^ r * Real.exp ((2 / 3 : ℝ) * x)) =
          (3 / 2 : ℝ) ^ r *
            (Real.exp (-x) * Real.exp ((2 / 3 : ℝ) * x)) by ring,
        hhalf, hthird]

/-- Closed source-scale specialization.  At degree `N = n+1` and every Euler frequency
`log(m+2)`, the scale `x = 6N log(m+2)` has retained damping `3N` and `2N`. -/
theorem reverseBesselEulerAtom_sixDegree_le (n m : ℕ) :
    let N := n + 1
    let r := (N + 1) / 2
    let L := Real.log (m + 2 : ℕ)
    Real.exp (-(6 * (N : ℝ) * L)) *
        reverseBesselNormalizedPoly N (6 * (N : ℝ) * L) ≤
      (2 : ℝ) ^ r * Real.exp (-(3 * (N : ℝ) * L)) +
        (3 / 2 : ℝ) ^ r * Real.exp (-(2 * (N : ℝ) * L)) := by
  let N := n + 1
  let r := (N + 1) / 2
  let L := Real.log (m + 2 : ℕ)
  have hM : (1 : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ m + 2)
  have hL : 0 ≤ L := by exact Real.log_nonneg hM
  have h := exp_neg_mul_reverseBesselNormalizedPoly_le_movingDamping
    N (x := 6 * (N : ℝ) * L) (by positivity)
  change Real.exp (-(6 * (N : ℝ) * L)) *
        reverseBesselNormalizedPoly N (6 * (N : ℝ) * L) ≤
      (2 : ℝ) ^ r * Real.exp (-(3 * (N : ℝ) * L)) +
        (3 / 2 : ℝ) ^ r * Real.exp (-(2 * (N : ℝ) * L))
  convert h using 1
  all_goals simp [r, Nat.add_comm]
  all_goals ring_nf

end


end RHTower
