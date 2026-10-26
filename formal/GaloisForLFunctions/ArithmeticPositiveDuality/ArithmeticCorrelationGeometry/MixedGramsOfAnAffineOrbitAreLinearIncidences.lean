import GaloisForLFunctions.ArithmeticPositiveDuality.ArithmeticCorrelationGeometry.TheBoundaryOfADilationIsTheArchimedeanPlace
import GaloisForLFunctions.SignedSuccessorArithmetic.TheSuccessorDilationCocycle

/-!
# Mixed Grams of an affine orbit are linear incidences

At a finite horizon the affine maps `g = (a, b) : j ↦ aj + b` push a source `v` to `A_g v`. The
**mixed Gram** of the orbit is the matrix `⟨A_g v, A_h w⟩`. It is the signed count of the linear
incidence `aj + b = ck + d` below the horizon (`horizonPairing_affine_affine`):

  `⟨A_{a,b} v, A_{c,d} w⟩ = Σ_{aj + b = ck + d ≤ N} v_j w_k`.

The three classical correlations are its faces: the successor face `a = c = 1` is the
autocorrelation at shift `d − b` (`horizonPairing_successor_successor`), the dilation face
`b = d = 0` is the correlation along the ratio `c/a` (`horizonPairing_dilation_dilation`), and the
mixed face `(a, b)` against the identity is the affine correlation `Σ_j v_j w_{aj+b}`.

* **Automatic positivity** (`gram_affine_nonneg`). Every finite mixed Gram of one source is
  positive semidefinite, whatever the source. A positive mixed Gram carries no arithmetic.
* **Dilation faces are gauge covariant** (`horizonPairing_dilation_signTwist`). Twisting a source
  on the positive cells by a completely multiplicative sign `f` multiplies the dilation entry
  along coprime `(a, c)` by the single character value `f(a) f(c)`: on the solutions `j = cm`,
  `k = am` the factor `f(m)²` cancels. Successor entries have no such law: their twist factor
  `f(j) f(j+h)` varies along the sum (`horizonPairing_successor_signTwist`).

So the dilation part of the mixed array is fixed by multiplicative data up to one character per
ratio, and the successor part is not: a mixed law constrains energy only if the successor part
is prescribed by the source.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open BiarithmeticGeometry SignedSuccessorArithmetic

/-! ### The incidence formula -/

/-- **The mixed Gram entry is a signed linear incidence count.** -/
theorem horizonPairing_affine_affine (N : ℕ) (a c : ℕ+) (b d : ℕ) (v w : HorizonSpace N) :
    horizonPairing N (horizonAffine N a b v) (horizonAffine N c d w) =
      ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
        if (a : ℕ) * j.val + b = (c : ℕ) * k.val + d ∧ (a : ℕ) * j.val + b ≤ N
        then v j * w k else 0 := by
  classical
  unfold horizonPairing
  simp_rw [horizonAffine_apply, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (a : ℕ) * j.val + b = (c : ℕ) * k.val + d ∧ (a : ℕ) * j.val + b ≤ N
  · rw [if_pos h, Finset.sum_eq_single ⟨(a : ℕ) * j.val + b, by omega⟩]
    · simp [h.1]
    · intro i _ hi
      have hne : i.val ≠ (a : ℕ) * j.val + b := fun e => hi (Fin.ext e)
      simp [hne]
    · exact fun hh => absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i.val = (a : ℕ) * j.val + b
    · by_cases h2 : i.val = (c : ℕ) * k.val + d
      · exact absurd ⟨h1 ▸ h2, h1 ▸ (Nat.lt_succ_iff.mp i.isLt)⟩ h
      · simp [h2]
    · simp [h1]

/-- **The successor face**: the autocorrelation at shift `d − b`. -/
theorem horizonPairing_successor_successor (N b d : ℕ) (v w : HorizonSpace N) :
    horizonPairing N (horizonAffine N 1 b v) (horizonAffine N 1 d w) =
      ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
        if j.val + b = k.val + d ∧ j.val + b ≤ N then v j * w k else 0 := by
  rw [horizonPairing_affine_affine]
  simp only [PNat.one_coe, one_mul]

/-- **The dilation face**: the correlation along the ratio `c/a`. -/
theorem horizonPairing_dilation_dilation (N : ℕ) (a c : ℕ+) (v w : HorizonSpace N) :
    horizonPairing N (horizonAffine N a 0 v) (horizonAffine N c 0 w) =
      ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
        if (a : ℕ) * j.val = (c : ℕ) * k.val ∧ (a : ℕ) * j.val ≤ N then v j * w k else 0 := by
  rw [horizonPairing_affine_affine]
  simp only [add_zero]

/-! ### Automatic positivity -/

theorem horizonPairing_sum_left {ι : Type*} (N : ℕ) (s : Finset ι) (u : ι → HorizonSpace N)
    (w : HorizonSpace N) :
    horizonPairing N (∑ i ∈ s, u i) w = ∑ i ∈ s, horizonPairing N (u i) w := by
  unfold horizonPairing
  simp_rw [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem horizonPairing_smul_left (N : ℕ) (r : ℝ) (u w : HorizonSpace N) :
    horizonPairing N (r • u) w = r * horizonPairing N u w := by
  unfold horizonPairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_assoc]

theorem horizonPairing_comm (N : ℕ) (u w : HorizonSpace N) :
    horizonPairing N u w = horizonPairing N w u := by
  unfold horizonPairing
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Automatic positivity.** Every finite mixed Gram of one source is positive semidefinite. -/
theorem gram_affine_nonneg {ι : Type*} (N : ℕ) (s : Finset ι) (g : ι → ℕ+ × ℕ) (r : ι → ℝ)
    (v : HorizonSpace N) :
    0 ≤ ∑ i ∈ s, ∑ i' ∈ s, r i * r i' *
      horizonPairing N (horizonAffine N (g i).1 (g i).2 v) (horizonAffine N (g i').1 (g i').2 v) := by
  set u : HorizonSpace N := ∑ i ∈ s, r i • horizonAffine N (g i).1 (g i).2 v with hu
  have hself : horizonPairing N u u = ∑ i ∈ s, ∑ i' ∈ s, r i * r i' *
      horizonPairing N (horizonAffine N (g i).1 (g i).2 v)
        (horizonAffine N (g i').1 (g i').2 v) := by
    rw [hu, horizonPairing_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [horizonPairing_smul_left, horizonPairing_comm, horizonPairing_sum_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [horizonPairing_smul_left, horizonPairing_comm]
    ring
  rw [← hself]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-! ### Gauge behaviour of the faces under completely multiplicative signs -/

/-- Twist a source cellwise by a sign function. -/
def signTwist (N : ℕ) (f : ℕ → ℤˣ) (v : HorizonSpace N) : HorizonSpace N :=
  fun j => ((f j.val : ℤ) : ℝ) * v j

theorem sign_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

/-- **Dilation faces are gauge covariant.** For a completely multiplicative sign `f`, coprime
multipliers `a, c` and sources vanishing at the origin, the dilation entry of the twisted sources
is the untwisted entry times `f(a) f(c)`. -/
theorem horizonPairing_dilation_signTwist (N : ℕ) (f : CMSign) {a c : ℕ+}
    (hac : Nat.Coprime a c) {v w : HorizonSpace N} (hv : v 0 = 0) :
    horizonPairing N (horizonAffine N a 0 (signTwist N f v)) (horizonAffine N c 0 (signTwist N f w)) =
      ((f a : ℤ) : ℝ) * ((f c : ℤ) : ℝ) *
        horizonPairing N (horizonAffine N a 0 v) (horizonAffine N c 0 w) := by
  rw [horizonPairing_dilation_dilation, horizonPairing_dilation_dilation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (a : ℕ) * j.val = (c : ℕ) * k.val ∧ (a : ℕ) * j.val ≤ N
  · rw [if_pos h, if_pos h]
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hj0 : j = 0 := Fin.ext hj
      rw [hj0, signTwist, hv]
      simp
    · -- `j = c m`, `k = a m`
      have hcj : (c : ℕ) ∣ j.val := (Nat.Coprime.symm hac).dvd_of_dvd_mul_left ⟨k.val, h.1⟩
      obtain ⟨m, hm⟩ := hcj
      have hk : k.val = (a : ℕ) * m := by
        have h1 := h.1
        rw [hm] at h1
        have : (c : ℕ) * k.val = (c : ℕ) * ((a : ℕ) * m) := by rw [← h1]; ring
        exact Nat.eq_of_mul_eq_mul_left c.pos this
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm; omega
        · exact h0
      have hfj : f j.val = f c * f m := by rw [hm]; exact f.map_mul c.pos hm0
      have hfk : f k.val = f a * f m := by rw [hk]; exact f.map_mul a.pos hm0
      simp only [signTwist]
      rw [hfj, hfk]
      push_cast
      have := sign_mul_self (f m)
      linear_combination ((f a : ℤ) : ℝ) * ((f c : ℤ) : ℝ) * (v j * w k) * this
  · rw [if_neg h, if_neg h, mul_zero]

/-- **Successor faces carry the varying factor `f(j) f(j+h)`.** -/
theorem horizonPairing_successor_signTwist (N h : ℕ) (f : ℕ → ℤˣ) (v w : HorizonSpace N) :
    horizonPairing N (horizonAffine N 1 0 (signTwist N f v)) (horizonAffine N 1 h (signTwist N f w)) =
      ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
        if j.val = k.val + h ∧ j.val ≤ N then
          ((f k.val : ℤ) : ℝ) * ((f (k.val + h) : ℤ) : ℝ) * (v j * w k) else 0 := by
  rw [horizonPairing_successor_successor]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [add_zero]
  split_ifs with hjk
  · simp only [signTwist]
    rw [hjk.1]
    ring
  · rfl

end GaloisForLFunctions.ArithmeticCorrelationGeometry
