import GaloisForLFunctions.HTGeometry.OrthogonalMomentPolynomials

/-!
# The Christoffel--Darboux kernel and its reproducing property

`cdKernel s n x` is the polynomial `y ↦ ∑_{k ≤ n} Qₖ(x) Qₖ(y) / hₖ`.  Against the moment form it
reproduces point evaluation on polynomials of degree `≤ n`:

`⟪p, cdKernel s n x⟫_s = p(x)`.

This is the abstract form of the reproducing-kernel identity, and it is the engine of Gauss
quadrature: applied to a polynomial vanishing at all but one node it isolates a single evaluation,
which is what produces the N-extremal masses.  It follows from `monicOrtho_expansion` — expanding
`p` in the orthogonal basis and evaluating at `x` gives exactly the same sum.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The Christoffel--Darboux kernel at level `n`, as a polynomial in the second variable. -/
noncomputable def cdKernel (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((monicOrtho s k).eval x / momentInner s (monicOrtho s k) (monicOrtho s k)) • monicOrtho s k

/-- **The reproducing property.**  The moment form against the kernel is point evaluation, on every
polynomial of degree at most `n`. -/
theorem momentInner_cdKernel (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) (p : Polynomial ℝ)
    (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    momentInner s p (cdKernel s n x) = p.eval x := by
  have hexp := monicOrtho_expansion h (n + 1) p hp
  rw [cdKernel, momentInner_sum_right]
  simp only [momentInner_smul_right]
  conv_rhs => rw [hexp]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul, momentInner_comm]
  ring

/-- The kernel evaluated on the diagonal is the weighted square sum. -/
theorem cdKernel_eval_self (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (cdKernel s n x).eval x
      = ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k) := by
  rw [cdKernel, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul]
  ring

/-- The diagonal value is strictly positive: the `k = 0` term already contributes `1 / h₀`. -/
theorem cdKernel_eval_self_pos (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    0 < (cdKernel s n x).eval x := by
  rw [cdKernel_eval_self]
  have hpos : ∀ k, 0 < momentInner s (monicOrtho s k) (monicOrtho s k) :=
    fun k => monicOrtho_inner_self_pos h k
  refine Finset.sum_pos' (fun k _ => div_nonneg (sq_nonneg _) (hpos k).le) ⟨0, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.succ_pos n)
  · have h0 : (monicOrtho s 0).eval x = 1 := by simp
    rw [h0]
    exact div_pos (by norm_num) (hpos 0)

/-- **The Christoffel function**: the reciprocal of the diagonal kernel value.  These are the masses
of the Gauss/N-extremal quadrature. -/
noncomputable def christoffel (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((cdKernel s n x).eval x)⁻¹

theorem christoffel_pos (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    0 < christoffel s n x :=
  inv_pos.mpr (cdKernel_eval_self_pos h n x)

theorem christoffel_mul_cdKernel (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    christoffel s n x * (cdKernel s n x).eval x = 1 :=
  inv_mul_cancel₀ (ne_of_gt (cdKernel_eval_self_pos h n x))

/-! ## Kernel structure

Symmetry, the degree bound, and the self-reproducing identity — the defining properties of a
reproducing kernel. -/

theorem cdKernel_eval (s : ℕ → ℝ) (n : ℕ) (x y : ℝ) :
    (cdKernel s n x).eval y
      = ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (monicOrtho s k).eval y /
          momentInner s (monicOrtho s k) (monicOrtho s k) := by
  rw [cdKernel, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul]
  ring

/-- **The kernel is symmetric.** -/
theorem cdKernel_symm (s : ℕ → ℝ) (n : ℕ) (x y : ℝ) :
    (cdKernel s n x).eval y = (cdKernel s n y).eval x := by
  rw [cdKernel_eval, cdKernel_eval]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The kernel has degree at most `n`. -/
theorem cdKernel_degree_lt (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (cdKernel s n x).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  rw [cdKernel]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun k hk => ?_
  refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
  rw [monicOrtho_degree s k]
  exact_mod_cast Finset.mem_range.mp hk

/-- **The self-reproducing identity.**  Pairing two kernels returns the kernel value: the hallmark of
a reproducing kernel. -/
theorem momentInner_cdKernel_cdKernel (h : PositiveMomentForm s) (n : ℕ) (x y : ℝ) :
    momentInner s (cdKernel s n x) (cdKernel s n y) = (cdKernel s n x).eval y := by
  rw [momentInner_comm,
    momentInner_cdKernel h n x (cdKernel s n y) (cdKernel_degree_lt s n y)]
  exact cdKernel_symm s n y x

/-- The Christoffel function is the reciprocal of the kernel's own moment norm. -/
theorem christoffel_eq_inv_momentInner (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    christoffel s n x = (momentInner s (cdKernel s n x) (cdKernel s n x))⁻¹ := by
  rw [christoffel, momentInner_cdKernel_cdKernel h n x x]

/-! ## The variational property

Cauchy--Schwarz for a positive definite moment form — proved from positivity alone, with no
representing measure — and the classical extremal characterisation of the Christoffel function:
it is the least moment norm among polynomials of degree at most `n` normalised at `x`. -/

/-- **Cauchy--Schwarz from positive definiteness.**  Unlike `momentInner_sq_le`, this needs no
representing measure: the discriminant of `t ↦ ⟪p + t q, p + t q⟫` does the work. -/
theorem momentInner_sq_le_of_posDef (h : PositiveMomentForm s) (p q : Polynomial ℝ) :
    (momentInner s p q) ^ (2 : ℕ) ≤ momentInner s p p * momentInner s q q := by
  have hquad : ∀ t : ℝ, 0 ≤ momentInner s q q * (t * t)
      + (2 * momentInner s p q) * t + momentInner s p p := by
    intro t
    have hexp : momentInner s (p + t • q) (p + t • q)
        = momentInner s q q * (t * t) + (2 * momentInner s p q) * t + momentInner s p p := by
      simp only [momentInner_add_left, momentInner_add_right, momentInner_smul_left,
        momentInner_smul_right]
      rw [momentInner_comm s q p]
      ring
    rw [← hexp]
    exact h.nonneg _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

/-- **The Christoffel variational property.**  Among polynomials of degree at most `n` taking the
value `1` at `x`, the Christoffel function is a lower bound for the moment norm. -/
theorem christoffel_le_momentInner_self (h : PositiveMomentForm s) (n : ℕ) (x : ℝ)
    (p : Polynomial ℝ) (hdeg : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) (hval : p.eval x = 1) :
    christoffel s n x ≤ momentInner s p p := by
  have hrep : momentInner s p (cdKernel s n x) = 1 := by
    rw [momentInner_cdKernel h n x p hdeg, hval]
  have hcs := momentInner_sq_le_of_posDef h p (cdKernel s n x)
  rw [hrep, momentInner_cdKernel_cdKernel h n x x] at hcs
  have hKpos := cdKernel_eval_self_pos h n x
  rw [christoffel, inv_eq_one_div, div_le_iff₀ hKpos]
  nlinarith [hcs]

/-- The bound is attained: the normalised kernel achieves the Christoffel value. -/
theorem christoffel_eq_momentInner_normalisedKernel (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    momentInner s (christoffel s n x • cdKernel s n x) (christoffel s n x • cdKernel s n x)
      = christoffel s n x := by
  rw [momentInner_smul_left, momentInner_smul_right,
    momentInner_cdKernel_cdKernel h n x x, christoffel]
  have hKpos := cdKernel_eval_self_pos h n x
  field_simp

/-- The normalised kernel is an admissible competitor: it has value `1` at `x`. -/
theorem normalisedKernel_eval_self (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    (christoffel s n x • cdKernel s n x).eval x = 1 := by
  rw [Polynomial.eval_smul, smul_eq_mul, christoffel]
  exact inv_mul_cancel₀ (ne_of_gt (cdKernel_eval_self_pos h n x))

/-! ## Positive definiteness of the kernel

The last defining property: the Christoffel--Darboux kernel is a positive semidefinite kernel.  It
follows from the self-reproducing identity, since the Gram sum *is* the moment norm of a single
polynomial. -/

theorem cdKernel_posSemidef {ι : Type*} (h : PositiveMomentForm s) (n : ℕ)
    (t : Finset ι) (x : ι → ℝ) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ t, ∑ j ∈ t, c i * c j * (cdKernel s n (x i)).eval (x j) := by
  have hF : momentInner s (∑ i ∈ t, c i • cdKernel s n (x i))
        (∑ j ∈ t, c j • cdKernel s n (x j))
      = ∑ i ∈ t, ∑ j ∈ t, c i * c j * (cdKernel s n (x i)).eval (x j) := by
    rw [momentInner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [momentInner_smul_left, momentInner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [momentInner_smul_right, momentInner_cdKernel_cdKernel h n (x i) (x j)]
    ring
  rw [← hF]
  exact h.nonneg _

/-- The diagonal dominates: `|K(x,y)| ≤ sqrt (K(x,x) K(y,y))`, the kernel Cauchy--Schwarz. -/
theorem cdKernel_sq_le (h : PositiveMomentForm s) (n : ℕ) (x y : ℝ) :
    ((cdKernel s n x).eval y) ^ (2 : ℕ)
      ≤ (cdKernel s n x).eval x * (cdKernel s n y).eval y := by
  have hcs := momentInner_sq_le_of_posDef h (cdKernel s n x) (cdKernel s n y)
  rw [momentInner_cdKernel_cdKernel h n x y, momentInner_cdKernel_cdKernel h n x x,
    momentInner_cdKernel_cdKernel h n y y] at hcs
  exact hcs

/-! ## Monotonicity

The kernel diagonal increases with the level, so the Christoffel function decreases.  Its limit is
the classical candidate for the mass an N-extremal measure puts at the point. -/

theorem cdKernel_eval_self_succ (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (cdKernel s (n + 1) x).eval x
      = (cdKernel s n x).eval x
        + (monicOrtho s (n + 1)).eval x ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) := by
  rw [cdKernel_eval_self, cdKernel_eval_self, Finset.sum_range_succ]

theorem cdKernel_eval_self_mono (h : PositiveMomentForm s) {m n : ℕ} (hmn : m ≤ n) (x : ℝ) :
    (cdKernel s m x).eval x ≤ (cdKernel s n x).eval x := by
  rw [cdKernel_eval_self, cdKernel_eval_self]
  have hpos : ∀ k, 0 < momentInner s (monicOrtho s k) (monicOrtho s k) :=
    fun k => monicOrtho_inner_self_pos h k
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro j hj
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hmn))
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro j _ _
  exact div_nonneg (sq_nonneg _) (hpos j).le

/-- **The Christoffel function is antitone in the level.** -/
theorem christoffel_antitone (h : PositiveMomentForm s) {m n : ℕ} (hmn : m ≤ n) (x : ℝ) :
    christoffel s n x ≤ christoffel s m x := by
  have hm := cdKernel_eval_self_pos h m x
  have hle := cdKernel_eval_self_mono h hmn x
  rw [christoffel, christoffel]
  gcongr

/-- The Christoffel values are bounded above by the level-zero value `h₀`. -/
theorem christoffel_le_h0 (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    christoffel s n x ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
  refine le_trans (christoffel_antitone h (Nat.zero_le n) x) ?_
  rw [christoffel, cdKernel_eval_self]
  have hx0 : (monicOrtho s 0).eval x = 1 := by simp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hx0, one_pow, zero_add]
  have hinv : (1 / momentInner s (monicOrtho s 0) (monicOrtho s 0))⁻¹
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [one_div, inv_inv]
  exact le_of_eq hinv

/-! ## The limit Christoffel function

Antitone and bounded below by zero, the level sequence `n ↦ λₙ(x)` converges.  Its limit needs no
analytic input beyond the positivity of the moment form, and it inherits the variational property of
each finite level: it is a lower bound for `⟪p, p⟫` over *all* polynomials normalised at `x`. -/

/-- The limit of the Christoffel function as the level grows. -/
noncomputable def christoffelLimit (s : ℕ → ℝ) (x : ℝ) : ℝ := ⨅ n, christoffel s n x

theorem antitone_christoffel (h : PositiveMomentForm s) (x : ℝ) :
    Antitone (fun n => christoffel s n x) :=
  fun _ _ hmn => christoffel_antitone h hmn x

theorem bddBelow_christoffel (h : PositiveMomentForm s) (x : ℝ) :
    BddBelow (Set.range fun n => christoffel s n x) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact (christoffel_pos h n x).le

theorem christoffelLimit_nonneg (h : PositiveMomentForm s) (x : ℝ) :
    0 ≤ christoffelLimit s x :=
  le_ciInf fun n => (christoffel_pos h n x).le

theorem christoffelLimit_le (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    christoffelLimit s x ≤ christoffel s n x :=
  ciInf_le (bddBelow_christoffel h x) n

theorem christoffelLimit_le_h0 (h : PositiveMomentForm s) (x : ℝ) :
    christoffelLimit s x ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
  le_trans (christoffelLimit_le h 0 x) (christoffel_le_h0 h 0 x)

/-- **The level sequence converges to the limit Christoffel function.** -/
theorem tendsto_christoffel (h : PositiveMomentForm s) (x : ℝ) :
    Filter.Tendsto (fun n => christoffel s n x) Filter.atTop
      (nhds (christoffelLimit s x)) :=
  tendsto_atTop_ciInf (antitone_christoffel h x) (bddBelow_christoffel h x)

/-- **Variational property of the limit.**  Every polynomial normalised at `x` has moment norm at
least `λ(x)`, with no degree restriction. -/
theorem christoffelLimit_le_momentInner_self (h : PositiveMomentForm s) (x : ℝ)
    (p : Polynomial ℝ) (hval : p.eval x = 1) :
    christoffelLimit s x ≤ momentInner s p p := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine ⟨p.natDegree, ?_⟩
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self _)
  exact le_trans (christoffelLimit_le h n x) (christoffel_le_momentInner_self h n x p hn hval)

end HTGeometry
