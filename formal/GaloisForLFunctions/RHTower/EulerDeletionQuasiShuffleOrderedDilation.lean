import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCrossDomain

/-!
# Exact ordered Euler deletion with its strict floor boundaries

Two finite divisor reindexings give a four-wedge formula for arbitrary input sequences. For
Dirichlet weights it specializes to the literal complex Euler-dilation factors. The wedge
inequality is strict: the upper inner cutoff is `(q*n-1)/p`, not `q*n/p`. All identities hold
before any zero or limiting argument. They impose no additional refinement-coherence law.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionOrderedDilation

def deletion (p : ℕ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  (blockDeletionCoefficient p n : ℂ) * x n

def orderedPrefix (x y : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (∑ m ∈ Finset.Icc 1 (n - 1), x m) * y n

def wedgePrefix (p q : ℕ) (x y : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N / q),
    (∑ m ∈ Finset.Icc 1 ((q * n - 1) / p), x m) * y n

/-- The floor cutoff encodes the strict ordering and excludes the diagonal. -/
theorem le_strict_floor_iff (p q m n : ℕ) (hp : 0 < p) (hqn : 0 < q * n) :
    m ≤ (q * n - 1) / p ↔ p * m < q * n := by
  rw [Nat.le_div_iff_mul_le hp, mul_comm m p]
  omega

/-- Deleting both coordinates preserves four distinct ordered regions. -/
theorem ordered_deletion_eq_wedges (p q N : ℕ) (hp : 0 < p) (hq : 0 < q)
    (x y : ℕ → ℂ) :
    orderedPrefix (deletion p x) (deletion q y) N =
      wedgePrefix 1 1 x y N -
      (p : ℂ) * wedgePrefix p 1 (fun m => x (p * m)) y N -
      (q : ℂ) * wedgePrefix 1 q x (fun n => y (q * n)) N +
      (p : ℂ) * q * wedgePrefix p q (fun m => x (p * m))
        (fun n => y (q * n)) N := by
  unfold orderedPrefix deletion
  have hswap (n : ℕ) :
      (∑ m ∈ Finset.Icc 1 (n - 1), (blockDeletionCoefficient p m : ℂ) * x m) *
          ((blockDeletionCoefficient q n : ℂ) * y n) =
        (blockDeletionCoefficient q n : ℂ) *
          ((∑ m ∈ Finset.Icc 1 (n - 1), (blockDeletionCoefficient p m : ℂ) * x m) *
            y n) := by ring
  simp_rw [hswap]
  rw [eulerDeletion_weighted_Icc_eq_dilation q N hq]
  simp_rw [eulerDeletion_weighted_Icc_eq_dilation p _ hp]
  simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [wedgePrefix, Nat.div_one, one_mul]
  ring

/-- Scalar factors pull out of either wedge coordinate without changing its domain. -/
theorem wedgePrefix_mul (p q N : ℕ) (a b : ℂ) (x y : ℕ → ℂ) :
    wedgePrefix p q (fun m => a * x m) (fun n => b * y n) N =
      (a * b) * wedgePrefix p q x y N := by
  simp only [wedgePrefix, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem wedgePrefix_mul_left (p q N : ℕ) (a : ℂ) (x y : ℕ → ℂ) :
    wedgePrefix p q (fun m => a * x m) y N = a * wedgePrefix p q x y N := by
  simpa using wedgePrefix_mul p q N a 1 x y

theorem wedgePrefix_mul_right (p q N : ℕ) (b : ℂ) (x y : ℕ → ℂ) :
    wedgePrefix p q x (fun n => b * y n) N = b * wedgePrefix p q x y N := by
  simpa using wedgePrefix_mul p q N 1 b x y

def dirichletWeight (s : ℂ) (n : ℕ) : ℂ := ((n : ℝ) : ℂ) ^ (-s)

theorem dirichletWeight_mul (s : ℂ) (p m : ℕ) :
    dirichletWeight s (p * m) = dirichletWeight s p * dirichletWeight s m := by
  simpa only [dirichletWeight, Nat.cast_mul, Complex.ofReal_mul] using
    Complex.mul_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ p)
      (by positivity : (0 : ℝ) ≤ m) (-s)

/-- Exact ordered Dirichlet dilation, with both exponents independent. -/
theorem ordered_dirichlet_deletion_eq_wedges
    (p q N : ℕ) (hp : 0 < p) (hq : 0 < q) (s t : ℂ) :
    orderedPrefix (deletion p (dirichletWeight s)) (deletion q (dirichletWeight t)) N =
      wedgePrefix 1 1 (dirichletWeight s) (dirichletWeight t) N -
      complexEulerDilationFactor p s *
        wedgePrefix p 1 (dirichletWeight s) (dirichletWeight t) N -
      complexEulerDilationFactor q t *
        wedgePrefix 1 q (dirichletWeight s) (dirichletWeight t) N +
      complexEulerDilationFactor p s * complexEulerDilationFactor q t *
        wedgePrefix p q (dirichletWeight s) (dirichletWeight t) N := by
  rw [ordered_deletion_eq_wedges p q N hp hq]
  simp_rw [dirichletWeight_mul]
  rw [wedgePrefix_mul_left, wedgePrefix_mul_right, wedgePrefix_mul]
  simp only [complexEulerDilationFactor, dirichletWeight]
  ring

theorem star_deletion (p n : ℕ) (x : ℕ → ℂ) :
    star (deletion p x n) = deletion p (fun k => star (x k)) n := by
  simp [deletion, star_mul']

/-- The actual Hermitian source has the conjugated multiplier in its outer coordinate. -/
theorem ordered_hermitian_deletion_eq_wedges
    (p q N : ℕ) (hp : 0 < p) (hq : 0 < q) (s t : ℂ) :
    orderedPrefix (deletion p (dirichletWeight s))
        (fun n => star (deletion q (dirichletWeight t) n)) N =
      wedgePrefix 1 1 (dirichletWeight s) (fun n => star (dirichletWeight t n)) N -
      complexEulerDilationFactor p s *
        wedgePrefix p 1 (dirichletWeight s) (fun n => star (dirichletWeight t n)) N -
      star (complexEulerDilationFactor q t) *
        wedgePrefix 1 q (dirichletWeight s) (fun n => star (dirichletWeight t n)) N +
      complexEulerDilationFactor p s * star (complexEulerDilationFactor q t) *
        wedgePrefix p q (dirichletWeight s) (fun n => star (dirichletWeight t n)) N := by
  simp_rw [star_deletion]
  rw [ordered_deletion_eq_wedges p q N hp hq]
  simp_rw [dirichletWeight_mul, star_mul']
  rw [wedgePrefix_mul_left, wedgePrefix_mul_right, wedgePrefix_mul]
  simp only [complexEulerDilationFactor, dirichletWeight, star_mul', star_natCast]
  ring

/-- The one-indexed ordered source is precisely the existing zero-indexed cross prefix. -/
theorem ordered_hermitian_eq_chronologicalCrossPrefix (p q N : ℕ) (s t : ℂ) :
    orderedPrefix (deletion (p+1) (dirichletWeight s))
        (fun n => star (deletion (q+1) (dirichletWeight t) n)) N =
      chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
        (eulerDeletionWeightedJump q t) N := by
  simp only [orderedPrefix, sum_Icc_eq_sum_range_succ, Nat.add_sub_cancel,
    chronologicalCrossPrefix, chronologicalCrossTerm, deletion, dirichletWeight,
    eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_one]

/-- The four ordered regions must be retained together under a common outer cutoff. -/
def hermitianDilationCombination (p q : ℕ) (s t : ℂ) (N : ℕ) : ℂ :=
  wedgePrefix 1 1 (dirichletWeight s) (fun n => star (dirichletWeight t n)) N -
  complexEulerDilationFactor p s *
    wedgePrefix p 1 (dirichletWeight s) (fun n => star (dirichletWeight t n)) N -
  star (complexEulerDilationFactor q t) *
    wedgePrefix 1 q (dirichletWeight s) (fun n => star (dirichletWeight t n)) N +
  complexEulerDilationFactor p s * star (complexEulerDilationFactor q t) *
    wedgePrefix p q (dirichletWeight s) (fun n => star (dirichletWeight t n)) N

theorem hermitianDilationCombination_eq_crossPrefix (p q N : ℕ) (s t : ℂ) :
    hermitianDilationCombination (p+1) (q+1) s t N =
      chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
        (eulerDeletionWeightedJump q t) N := by
  rw [← ordered_hermitian_eq_chronologicalCrossPrefix p q N s t]
  exact (ordered_hermitian_deletion_eq_wedges (p+1) (q+1) N
    (Nat.succ_pos _) (Nat.succ_pos _) s t).symm

/-- The complete ordered dilation expression converges on the zero-independent domain.
No separate limit or rearrangement of its four terms is assumed. -/
theorem hermitianDilationCombination_converges (p q : ℕ) (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) (hst : 1 < s.re + t.re) :
    ∃ L : ℂ, Tendsto (hermitianDilationCombination (p+1) (q+1) s t)
      atTop (nhds L) := by
  obtain ⟨L, hL⟩ := tendsto_chronologicalCrossPrefix_eulerDeletion_domain p q s t hs ht hst
  refine ⟨L, hL.congr (fun N => ?_)⟩
  exact (hermitianDilationCombination_eq_crossPrefix p q N s t).symm

end RHTower.DeletionOrderedDilation

