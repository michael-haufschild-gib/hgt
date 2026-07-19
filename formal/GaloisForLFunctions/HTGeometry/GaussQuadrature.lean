import GaloisForLFunctions.HTGeometry.GaussQuadratureNodes
import GaloisForLFunctions.HTGeometry.ChristoffelKernel
import GaloisForLFunctions.HTGeometry.ChristoffelDarboux

/-!
# Gauss quadrature

The `n+1` roots of `monicOrtho s (n+1)`, weighted by the Christoffel function, reproduce the moment
functional on every polynomial of degree at most `2n+1`:

`momentFunctional s p = ∑_{ξ} λₙ(ξ) · p(ξ)`.

The proof has two halves.  On degree `≤ n` the normalised Christoffel--Darboux kernels
`gaussBasis s n ξ = λₙ(ξ) • K_ξ` form a Lagrange basis for the node set: each takes the value `1`
at its own node, and `0` at the others because the Christoffel--Darboux identity makes the kernel
vanish between two distinct roots of `monicOrtho s (n+1)`.  Interpolating in that basis and
applying the
moment functional termwise gives exactness, since each basis element has moment value exactly its
Christoffel weight.

Degree `≤ 2n+1` then follows by division: writing `p = ρ + Q q` with `Q = monicOrtho s (n+1)` and
`deg ρ, deg q ≤ n`, the term `Q q` contributes nothing to either side — nothing to the moment
functional because `Q` is orthogonal to every polynomial of degree `≤ n`, and nothing to the sum
because `Q` vanishes at every node.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The kernel vanishes between distinct nodes.**  At two distinct roots of `monicOrtho s (n+1)`
the Christoffel--Darboux numerator vanishes identically, so the kernel value must. -/
theorem cdKernel_eval_eq_zero_of_root_ne (h : PositiveMomentForm s) (n : ℕ) {x y : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0) (hy : (monicOrtho s (n + 1)).eval y = 0)
    (hxy : x ≠ y) : (cdKernel s n x).eval y = 0 := by
  have hcd := christoffelDarboux h n x y
  have hzero : ((monicOrtho s (n + 1)).eval x * (monicOrtho s n).eval y -
      (monicOrtho s n).eval x * (monicOrtho s (n + 1)).eval y) /
      momentInner s (monicOrtho s n) (monicOrtho s n) = 0 := by
    rw [hx, hy]; ring
  rw [hzero] at hcd
  rw [cdKernel_eval]
  rcases mul_eq_zero.mp hcd with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hxy
  · exact h2

/-- The Lagrange basis attached to the Gauss nodes: the Christoffel-normalised kernel. -/
noncomputable def gaussBasis (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : Polynomial ℝ :=
  christoffel s n x • cdKernel s n x

theorem gaussBasis_degree_lt (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (gaussBasis s n x).degree < ((n + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt (degree_smul_le _ _) (cdKernel_degree_lt s n x)

theorem gaussBasis_eval_self (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    (gaussBasis s n x).eval x = 1 :=
  normalisedKernel_eval_self h n x

theorem gaussBasis_eval_of_ne (h : PositiveMomentForm s) (n : ℕ) {x y : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0) (hy : (monicOrtho s (n + 1)).eval y = 0)
    (hxy : x ≠ y) : (gaussBasis s n x).eval y = 0 := by
  rw [gaussBasis, eval_smul, smul_eq_mul,
    cdKernel_eval_eq_zero_of_root_ne h n hx hy hxy, mul_zero]

/-- **Each basis element has moment value its Christoffel weight.**  The kernel reproduces the
constant polynomial `1`, whose value at any point is `1`. -/
theorem momentFunctional_gaussBasis (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    momentFunctional s (gaussBasis s n x) = christoffel s n x := by
  have hone : (1 : Polynomial ℝ).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_one]
    exact_mod_cast Nat.succ_pos n
  have hrep : momentInner s 1 (cdKernel s n x) = 1 := by
    simpa using momentInner_cdKernel h n x 1 hone
  have hK : momentFunctional s (cdKernel s n x) = 1 := by
    rw [← hrep, momentInner_def, one_mul]
  rw [gaussBasis, momentFunctional_smul, hK, mul_one]

/-- **Lagrange interpolation at the Gauss nodes.**  A polynomial of degree at most `n` is recovered
from its values at the `n+1` nodes. -/
theorem gauss_interpolation (h : PositiveMomentForm s) (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    p = ∑ x ∈ gaussNodes s n, p.eval x • gaussBasis s n x := by
  classical
  have hsumdeg : (∑ x ∈ gaussNodes s n, p.eval x • gaussBasis s n x).degree
      < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
    intro x _
    exact lt_of_le_of_lt (degree_smul_le _ _) (gaussBasis_degree_lt s n x)
  set D := p - ∑ x ∈ gaussNodes s n, p.eval x • gaussBasis s n x with hDdef
  have hDdeg : D.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (degree_sub_le _ _) (max_lt hp hsumdeg)
  have hDeval : ∀ y ∈ gaussNodes s n, D.eval y = 0 := by
    intro y hy
    have hyroot : (monicOrtho s (n + 1)).eval y = 0 := (mem_gaussNodes_iff n y).mp hy
    have hsum : ∑ x ∈ gaussNodes s n, (p.eval x • gaussBasis s n x).eval y = p.eval y := by
      rw [Finset.sum_eq_single y]
      · rw [eval_smul, smul_eq_mul, gaussBasis_eval_self h n y, mul_one]
      · intro x hx hxy
        have hxroot : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).mp hx
        rw [eval_smul, smul_eq_mul, gaussBasis_eval_of_ne h n hxroot hyroot hxy, mul_zero]
      · intro hy'
        exact absurd hy hy'
    rw [hDdef, eval_sub, eval_finsetSum, hsum, sub_self]
  have hDzero : D = 0 := by
    by_cases hD0 : D = 0
    · exact hD0
    · refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D (gaussNodes s n) hDeval ?_
      rw [gaussNodes_card h n]
      exact (natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  rw [hDdef] at hDzero
  exact sub_eq_zero.mp hDzero

/-- **Exactness on degree at most `n`.** -/
theorem momentFunctional_eq_gaussSum_of_degree_lt (h : PositiveMomentForm s) (n : ℕ)
    (p : Polynomial ℝ) (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    momentFunctional s p = ∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x := by
  conv_lhs => rw [gauss_interpolation h n p hp]
  rw [momentFunctional_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [momentFunctional_smul, momentFunctional_gaussBasis h n x]
  ring

/-- **Gauss quadrature is exact on degree at most `2n+1`.**  Dividing by `monicOrtho s (n+1)` leaves
a remainder of degree at most `n`; the quotient term is invisible to both sides. -/
theorem momentFunctional_eq_gaussSum (h : PositiveMomentForm s) (n : ℕ)
    (p : Polynomial ℝ) (hp : p.degree < ((2 * n + 2 : ℕ) : WithBot ℕ)) :
    momentFunctional s p = ∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x := by
  classical
  have hQm : (monicOrtho s (n + 1)).Monic := monicOrtho_monic s (n + 1)
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
  have hsplit : p %ₘ monicOrtho s (n + 1)
      + monicOrtho s (n + 1) * (p /ₘ monicOrtho s (n + 1)) = p :=
    modByMonic_add_div p (monicOrtho s (n + 1))
  set q := p /ₘ monicOrtho s (n + 1) with hqdef
  set r := p %ₘ monicOrtho s (n + 1) with hrdef
  have hrdeg : r.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hlt := degree_modByMonic_lt p hQm
    rw [monicOrtho_degree s (n + 1)] at hlt
    exact hlt
  have hqdeg : q.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    by_cases hq0 : q = 0
    · rw [hq0, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hp0 : p ≠ 0 := by
        intro hpz
        refine hq0 ?_
        rw [hqdef, hpz]
        simp
      have hnd : q.natDegree = p.natDegree - (n + 1) := by
        rw [hqdef, natDegree_divByMonic p hQm, hQnd]
      have hpnd : p.natDegree < 2 * n + 2 := (natDegree_lt_iff_degree_lt hp0).mpr hp
      refine (natDegree_lt_iff_degree_lt hq0).mp ?_
      omega
  have horth : momentFunctional s (monicOrtho s (n + 1) * q) = 0 := by
    have hz := monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl q hqdeg
    rwa [momentInner_def] at hz
  rw [← hsplit, momentFunctional_add, horth, add_zero,
    momentFunctional_eq_gaussSum_of_degree_lt h n r hrdeg]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxroot : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).mp hx
  rw [eval_add, eval_mul, hxroot, zero_mul, add_zero]

end HTGeometry
