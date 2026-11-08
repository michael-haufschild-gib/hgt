import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.RHTower.HyperellipticRiemannHypothesis

/-!
# The count law of a true curve at every genus

**A crude count is the count law.** For a curve datum of genus `g`, the channel numbers extend to a
count law at every level of the tower iff the point counts deviate from `qⁿ + 1` by at most
`C qⁿᐟ²` at every level, for some constant `C` (`towerCountLaw_iff_crude_bound`). The constant is
irrelevant: power-sum elimination improves any uniform bound to the sharp one, and the functional
equation places every mode on the circle. So a producer that bounds the channels crudely, at every
level, produces the count law.

**True curves of every genus.** Stepanov's producer does this for the split hyperelliptic curves
`y² = f(x)`, `deg f = 2g + 1`, in odd characteristic (`RHTower.Hyperelliptic`). Over every finite
extension `E` the channel numbers `g`, `g |E|`, `N_E + (g − 1)(|E| + 1)` of the curve, with
`N_E` its number of points including the one at infinity, extend to a count of all probes
(`splitHyperelliptic_countLaw`). This is the count side of Weil's theorem at every genus, obtained
from channels: the genus-one case is Manin's height (`ArithmeticScatteringHolography`); here the count
comes from Stepanov's auxiliary polynomial, without heights and without Castelnuovo–Severi.
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri

/-! ### The self-improvement of counts -/

section CurveData

variable {ι : Type*} [Fintype ι]

/-- **Power-sum elimination with any constant.** Traces bounded uniformly at every level put every mode
on the circle. -/
theorem unitary_of_crude_trace_bound (D : CurveDatum ι) {C : ℝ}
    (h : ∀ n, 1 ≤ n → |D.trace n| ≤ C) : ∀ i, ‖D.β i‖ = 1 := by
  have hle : ∀ i, ‖D.β i‖ ≤ 1 := by
    intro i
    refine RHTower.WeilKloosterman.norm_le_of_power_sums_bound Finset.univ D.β (C := C) (m0 := 1)
      zero_le_one (fun m hm => ?_) i (Finset.mem_univ i)
    rw [one_pow, mul_one]
    have e : ∑ i ∈ Finset.univ, D.β i ^ m = D.powerSum m := rfl
    rw [e, D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
    exact h m hm
  intro i
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i)), hle i, hle (D.fePerm i)]

/-- The deviation of the point count from `qⁿ + 1` is `qⁿᐟ²` times the trace. -/
theorem abs_pointCount_sub (D : CurveDatum ι) (n : ℕ) :
    |D.pointCount n - (D.q ^ n + 1)| = D.sqrtq ^ n * |D.trace n| := by
  rw [CurveDatum.pointCount, show D.q ^ n + 1 - D.sqrtq ^ n * D.trace n - (D.q ^ n + 1) =
    -(D.sqrtq ^ n * D.trace n) by ring, abs_neg, abs_mul, abs_of_pos (pow_pos D.sqrtq_pos n)]

/-- **A crude count is the count law.** The channel numbers of a curve datum of genus `g` extend to a
count law at every level iff the point counts are within `C qⁿᐟ²` of `qⁿ + 1` at every level, for
some `C`. -/
theorem towerCountLaw_iff_crude_bound (D : CurveDatum ι) {g Q : ℕ} (hg : Fintype.card ι = 2 * g)
    (hg0 : 0 < g) (hQ : D.q = Q) {N : ℕ → ℕ} (hN : ∀ n, (N n : ℝ) = D.pointCount n) :
    (∀ n, 1 ≤ n → ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧ K 1 0 = g * Q ^ n ∧
      K 1 1 = N n + (g - 1) * (Q ^ n + 1)) ↔
      ∃ C : ℝ, ∀ n, 1 ≤ n → |(N n : ℝ) - (D.q ^ n + 1)| ≤ C * D.sqrtq ^ n := by
  rw [towerCountLaw_iff_unitary D hg hg0 hQ hN]
  constructor
  · intro hU
    refine ⟨Fintype.card ι, fun n _ => ?_⟩
    rw [hN, abs_pointCount_sub, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_trace_le_of_unitary D hU n) (pow_nonneg D.sqrtq_pos.le n)
  · rintro ⟨C, hC⟩
    refine unitary_of_crude_trace_bound D (C := C) fun n hn => ?_
    have h := hC n hn
    rw [hN, abs_pointCount_sub] at h
    have hs : 0 < D.sqrtq ^ n := pow_pos D.sqrtq_pos n
    rw [mul_comm C] at h
    exact le_of_mul_le_mul_left h hs

end CurveData

/-! ### True hyperelliptic curves -/

section Hyperelliptic

open GaloisForLFunctions.RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- **The count law of a true curve, at every genus and every level.** For `y² = f(x)` with `f` split,
squarefree, of degree `2g + 1`, in odd characteristic, and every finite extension `E`, the channel
numbers `g`, `g |E|`, `N_E + (g − 1)(|E| + 1)` extend to a count law, where `N_E` counts the points over
`E` including the point at infinity. -/
theorem splitHyperelliptic_countLaw (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) {g : ℕ} (hdeg : f.natDegree = 2 * g + 1) (hg : 1 ≤ g) (E : Type*) [Field E]
    [Fintype E] [Algebra F E] :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧ K 1 0 = g * Fintype.card E ∧
      K 1 1 = ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card + 1) +
        (g - 1) * (Fintype.card E + 1) := by
  have hodd : Odd f.natDegree := ⟨g, hdeg⟩
  set A : ℕ := (univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card
  set Q : ℕ := Fintype.card E
  have hbound := abs_card_points_sub_le_splitHyperelliptic hF hsq hsplit hodd E
  rw [hdeg, show 2 * g + 1 - 1 = 2 * g by omega] at hbound
  -- the trace `a = |E| − A` obeys the Weil bound `a² ≤ 4 g² |E|`
  set a : ℤ := (Q : ℤ) - A
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hweil : a ^ 2 ≤ 4 * (g : ℤ) ^ 2 * Q := by
    have h1 : |(a : ℝ)| ≤ (2 * g : ℕ) * Real.sqrt Q := by
      have : (a : ℝ) = -((A : ℝ) - Q) := by simp [a]
      rw [this, abs_neg]
      exact hbound
    have h2 : (a : ℝ) ^ 2 ≤ ((2 * g : ℕ) * Real.sqrt Q) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [mul_pow, Real.sq_sqrt hQ0] at h2
    have : ((a ^ 2 : ℤ) : ℝ) ≤ ((4 * (g : ℤ) ^ 2 * Q : ℤ) : ℝ) := by
      push_cast at h2 ⊢
      linarith
    exact_mod_cast this
  obtain ⟨K, hK, h01, h10, h11⟩ :=
    (exists_genusCountLaw_iff (g := (g : ℤ)) (Q := (Q : ℤ)) (a := a) (by exact_mod_cast hg)).mpr hweil
  refine ⟨K, hK, by exact_mod_cast h01, by exact_mod_cast h10, ?_⟩
  have : (K 1 1 : ℤ) = ((A + 1 + (g - 1) * (Q + 1) : ℕ) : ℤ) := by
    rw [h11]
    simp only [a]
    push_cast [Nat.cast_sub hg]
    ring
  exact_mod_cast this

end Hyperelliptic

end GaloisForLFunctions.CountingHolography

end
