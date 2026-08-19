import GaloisForLFunctions.HTGeometry.PathLaplacianRootedCofactor
import GaloisForLFunctions.HTGeometry.CycleTwistedTorsion
import Mathlib

/-!
# The prime-support deformation as rooted Hodge cofactors of a flag path

The prefix flag of a prime support of cardinality `n + 1`, coned by the full source, has the path
`P_{n+1}` as incidence graph.  With common edge conductance `1 - t` the rooted cofactors of its
weighted Hodge Laplacian are all equal to `(1 - t) ^ n`, so their sum is the marked support
deformation `(n + 1) (1 - t) ^ n`; the first nonvanishing normal derivative at `t = 1` is of order
`n` and equals `(n + 1) (-1) ^ n n !`.

A chamber carries no phase: the twisted flag-path cofactors are gauge equivalent to the untwisted
ones.  The minimal phase-bearing successor is a cycle, whose torsion is the holonomy defect.  For
positive prime monomial holonomies `exp (-i z log N)` with `N > 1`, torsion cohomology jumps
exactly on the centred critical line, and the finite squarefree Euler product is the product of the
one-edge torsions with holonomy `-p^{-s}`.
-/

open Complex GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The marked prime-support deformation `M_n(t) = n (1 - t) ^ (n - 1)`. -/
def primeSupportDeformation (n : ℕ) (t : ℂ) : ℂ := (n : ℂ) * (1 - t) ^ (n - 1)

/-- **The support deformation is the sum of the rooted flag-path Hodge cofactors.** -/
theorem primeSupportDeformation_eq_sum_det_rootedPathLaplacian (n : ℕ) (t : ℂ) :
    primeSupportDeformation (n + 1) t
      = ∑ r : Fin (n + 1), (rootedPathLaplacian ℂ (1 - t) n r).det := by
  rw [sum_det_rootedPathLaplacian, primeSupportDeformation]
  simp

/-- Every single rooted cofactor of the flag path is the product of the edge conductances. -/
theorem det_rootedPathLaplacian_flag (n : ℕ) (t : ℂ) (r : Fin (n + 1)) :
    (rootedPathLaplacian ℂ (1 - t) n r).det = (1 - t) ^ n :=
  det_rootedPathLaplacian ℂ (1 - t) n r

/-- The deformation as a polynomial. -/
def primeSupportDeformationPoly (n : ℕ) : Polynomial ℂ :=
  Polynomial.C (n : ℂ) * (1 - Polynomial.X) ^ (n - 1)

theorem iterate_derivative_one_sub_X_pow (m : ℕ) :
    (Polynomial.derivative^[m] ((1 - Polynomial.X : Polynomial ℂ) ^ m))
      = Polynomial.C ((-1) ^ m * ((m.factorial : ℕ) : ℂ)) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hderiv : Polynomial.derivative ((1 - Polynomial.X : Polynomial ℂ) ^ (k + 1))
        = Polynomial.C (-(k + 1 : ℂ)) * (1 - Polynomial.X) ^ k := by
      rw [Polynomial.derivative_pow]
      simp
      ring
    rw [Function.iterate_succ_apply, hderiv, Polynomial.iterate_derivative_C_mul, ih,
      ← Polynomial.C_mul]
    congr 1
    push_cast [Nat.factorial_succ]
    ring

/-- **Top normal derivative of the marked deformation.**  The first nonvanishing derivative at the
boundary point `t = 1` has order the number of chamber edges. -/
theorem eval_iterate_derivative_primeSupportDeformationPoly (n : ℕ) :
    (Polynomial.derivative^[n] (primeSupportDeformationPoly (n + 1))).eval 1
      = ((n : ℂ) + 1) * (-1) ^ n * ((n.factorial : ℕ) : ℂ) := by
  rw [primeSupportDeformationPoly]
  simp only [Nat.add_sub_cancel]
  rw [Polynomial.iterate_derivative_C_mul, iterate_derivative_one_sub_X_pow]
  simp
  ring

theorem primeSupportDeformationPoly_eval (n : ℕ) (t : ℂ) :
    (primeSupportDeformationPoly n).eval t = primeSupportDeformation n t := by
  simp [primeSupportDeformationPoly, primeSupportDeformation]

/-- The holonomy of a positive prime monomial: `exp (-i z log N)`. -/
def primeMonomialHolonomy (N : ℝ) (z : ℂ) : ℂ := Complex.exp (-(Complex.I * z * (Real.log N : ℂ)))

/-- **Positive prime monomial holonomies are trivial only on the centred critical line.** -/
theorem im_eq_zero_of_primeMonomialHolonomy_eq_one {N : ℝ} (hN : 1 < N) {z : ℂ}
    (h : primeMonomialHolonomy N z = 1) : z.im = 0 := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hnorm : Real.exp ((-(Complex.I * z * (Real.log N : ℂ))).re) = 1 := by
    have := congrArg norm h
    rwa [primeMonomialHolonomy, Complex.norm_exp, norm_one] at this
  have hre : (-(Complex.I * z * (Real.log N : ℂ))).re = z.im * Real.log N := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre] at hnorm
  have hzero : z.im * Real.log N = 0 := by
    have hl := congrArg Real.log hnorm
    rwa [Real.log_exp, Real.log_one] at hl
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exact h1
  · exact absurd h2 (ne_of_gt hlog)

/-- The holonomy of a positive prime-power monomial is the monomial holonomy of its norm. -/
theorem prod_primeCharacter_pow_eq_primeMonomialHolonomy
    (S : Finset Nat.Primes) (m : Nat.Primes → ℕ) (z : ℂ) :
    (∏ p ∈ S, (Complex.exp (-(Complex.I * z * ((Real.log ((p : ℕ) : ℝ)) : ℂ)))) ^ m p)
      = primeMonomialHolonomy (∏ p ∈ S, ((p : ℕ) : ℝ) ^ m p) z := by
  have hne : ∀ p ∈ S, (((p : ℕ) : ℝ) ^ m p) ≠ 0 := by
    intro p _
    refine pow_ne_zero _ ?_
    exact_mod_cast p.2.pos.ne'
  have hterm : ∀ p ∈ S,
      (Complex.exp (-(Complex.I * z * ((Real.log ((p : ℕ) : ℝ)) : ℂ)))) ^ m p
        = Complex.exp (-(Complex.I * z * ((Real.log (((p : ℕ) : ℝ) ^ m p)) : ℂ))) := by
    intro p _
    rw [← Complex.exp_nat_mul, Real.log_pow]
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl hterm, ← Complex.exp_sum, primeMonomialHolonomy,
    Real.log_prod hne]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- The norm of a nonempty positive prime-power packet exceeds one. -/
theorem one_lt_prod_prime_pow {S : Finset Nat.Primes} {m : Nat.Primes → ℕ}
    (hS : S.Nonempty) (hm : ∀ p ∈ S, 0 < m p) :
    1 < ∏ p ∈ S, ((p : ℕ) : ℝ) ^ m p := by
  classical
  obtain ⟨q, hq⟩ := hS
  have hsplit : (∏ p ∈ S, ((p : ℕ) : ℝ) ^ m p)
      = (((q : ℕ) : ℝ) ^ m q) * ∏ p ∈ S.erase q, ((p : ℕ) : ℝ) ^ m p :=
    (Finset.mul_prod_erase S _ hq).symm
  have hq1 : (1 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.one_lt
  have h1 : 1 < ((q : ℕ) : ℝ) ^ m q := one_lt_pow₀ hq1 (Nat.pos_iff_ne_zero.mp (hm q hq))
  have h2 : (1 : ℝ) ≤ ∏ p ∈ S.erase q, ((p : ℕ) : ℝ) ^ m p := by
    refine Finset.one_le_prod fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    exact one_le_pow₀ hp1
  have hqpos : (0 : ℝ) < ((q : ℕ) : ℝ) ^ m q := by positivity
  calc (1 : ℝ) < ((q : ℕ) : ℝ) ^ m q := h1
    _ = ((q : ℕ) : ℝ) ^ m q * 1 := (mul_one _).symm
    _ ≤ ((q : ℕ) : ℝ) ^ m q * ∏ p ∈ S.erase q, ((p : ℕ) : ℝ) ^ m p :=
        mul_le_mul_of_nonneg_left h2 hqpos.le
    _ = ∏ p ∈ S, ((p : ℕ) : ℝ) ^ m p := hsplit.symm

/-- A one-edge cycle with transport `-p^{-s}` has torsion the local squarefree Euler factor. -/
theorem det_cycleDifferential_squarefree_factor (p : Nat.Primes) (s : ℂ) :
    (cycleDifferential 0 (fun _ => 1) (fun _ => -((p : ℕ) : ℂ) ^ (-s))).det
      = 1 + ((p : ℕ) : ℂ) ^ (-s) := by
  rw [det_cycleDifferential]
  have hcard : Fintype.card (CycleIndex 0) = 1 := by simp [CycleIndex]
  have hsub : ∀ i j : CycleIndex 0, i = j := fun i j =>
    Fintype.card_le_one_iff.mp (le_of_eq hcard) i j
  have h1 : (∏ _j : CycleIndex 0, (1 : ℂ)) = 1 := Finset.prod_const_one
  have h2 : cycleHolonomy (fun _ : CycleIndex 0 => -((p : ℕ) : ℂ) ^ (-s))
      = -((p : ℕ) : ℂ) ^ (-s) := by
    rw [cycleHolonomy, Finset.prod_eq_single (0 : CycleIndex 0)
      (fun b _ hb => absurd (hsub b 0) hb) (fun h => absurd (Finset.mem_univ _) h)]
  rw [h1, h2]
  ring

/-- **The finite squarefree Euler product is the torsion of the source apartments.** -/
theorem prod_det_cycleDifferential_squarefree (S : Finset Nat.Primes) (s : ℂ) :
    (∏ p ∈ S, (cycleDifferential 0 (fun _ => 1) (fun _ => -((p : ℕ) : ℂ) ^ (-s))).det)
      = ∏ p ∈ S, (1 + ((p : ℕ) : ℂ) ^ (-s)) :=
  Finset.prod_congr rfl fun p _ => det_cycleDifferential_squarefree_factor p s

/-- **Finite acyclicity in the open right half plane.**  No source apartment has cohomology when
the Euler variable has positive real part. -/
theorem det_cycleDifferential_squarefree_ne_zero {p : Nat.Primes} {s : ℂ} (hs : 0 < s.re) :
    (cycleDifferential 0 (fun _ => 1) (fun _ => -((p : ℕ) : ℂ) ^ (-s))).det ≠ 0 := by
  rw [det_cycleDifferential_squarefree_factor]
  have hp : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  intro hzero
  have : ((p : ℕ) : ℂ) ^ (-s) = -1 := by linear_combination hzero
  rw [this] at hnorm
  simp at hnorm

/-- **Positive prime-apartment torsion jumps only on the centred critical line.**  If a cycle with
nonvanishing edge weights has the holonomy of a nonempty positive prime-power packet and its
torsion vanishes, the centred height is real. -/
theorem im_eq_zero_of_det_cycleDifferential_eq_zero {S : Finset Nat.Primes}
    {m : Nat.Primes → ℕ} (hS : S.Nonempty) (hm : ∀ p ∈ S, 0 < m p) {n : ℕ}
    {w u : CycleIndex n → ℂ} (hw : ∀ j, w j ≠ 0) {z : ℂ}
    (hu : cycleHolonomy u
      = ∏ p ∈ S, (Complex.exp (-(Complex.I * z * ((Real.log ((p : ℕ) : ℝ)) : ℂ)))) ^ m p)
    (hdet : (cycleDifferential n w u).det = 0) : z.im = 0 := by
  have hone : cycleHolonomy u = 1 := (det_cycleDifferential_eq_zero_iff hw).mp hdet
  have hpacket : primeMonomialHolonomy (∏ p ∈ S, ((p : ℕ) : ℝ) ^ m p) z = 1 := by
    rw [← prod_primeCharacter_pow_eq_primeMonomialHolonomy, ← hu, hone]
  exact im_eq_zero_of_primeMonomialHolonomy_eq_one (one_lt_prod_prime_pow hS hm) hpacket

end

end RHTower
