import GaloisForLFunctions.HTGeometry.GaussResolventError

/-!
# The first Hausdorff-difference form of a positive moment functional

For a positive moment functional with Gauss nodes `x_i` and Christoffel weights `ω_i`, the first
Hausdorff-difference form at a mass `y` is

`E_y(q) = L((1 - yX)·q²) = ∑ ω_i (1 - y x_i) q(x_i)²`,

exact on polynomials of degree at most `n` because the integrand then has degree at most `2n+1`.
Its value on the unnormalised Lagrange quotient `p/(X - x_i)` is `(1 - y x_i)` times that
quotient's own energy, so the sign of a single diagonal entry is exactly the sign of `1 - y x_i` —
the node's position relative to the moving apex `1/y`.
-/

open Polynomial

noncomputable section

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The first Hausdorff-difference form at mass `y`. -/
def hausdorffDifferenceForm (s : ℕ → ℝ) (y : ℝ) (q : Polynomial ℝ) : ℝ :=
  momentFunctional s ((1 - Polynomial.C y * Polynomial.X) * q ^ (2 : ℕ))

theorem natDegree_hausdorffIntegrand_le (y : ℝ) (q : Polynomial ℝ) :
    ((1 - Polynomial.C y * Polynomial.X) * q ^ (2 : ℕ)).natDegree ≤ 1 + 2 * q.natDegree := by
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : (1 - Polynomial.C y * Polynomial.X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp only [Polynomial.natDegree_one, max_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    simp
  have h2 : (q ^ (2 : ℕ)).natDegree ≤ 2 * q.natDegree := by
    rw [Polynomial.natDegree_pow]
  omega

/-- **(SAHI.3) The Hausdorff-difference form is the signed quadrature sum.** -/
theorem hausdorffDifferenceForm_eq_gaussSum (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ n) :
    hausdorffDifferenceForm s y q
      = ∑ x ∈ gaussNodes s n, christoffel s n x * ((1 - y * x) * (q.eval x) ^ (2 : ℕ)) := by
  have hdeg : ((1 - Polynomial.C y * Polynomial.X) * q ^ (2 : ℕ)).degree
      < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have hnd := natDegree_hausdorffIntegrand_le y q
    exact_mod_cast Nat.lt_succ_of_le (by omega)
  rw [hausdorffDifferenceForm, momentFunctional_eq_gaussSum h n _ hdeg]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

/-! ## The Lagrange quotient at a node -/

/-- The unnormalised Lagrange quotient `p/(X - x₀)` of the orthogonal polynomial at a node. -/
def lagrangeQuotient (s : ℕ → ℝ) (n : ℕ) (x₀ : ℝ) : Polynomial ℝ :=
  nodeCofactor (monicOrtho s (n + 1)) x₀

theorem natDegree_lagrangeQuotient (s : ℕ → ℝ) (n : ℕ) (x₀ : ℝ) :
    (lagrangeQuotient s n x₀).natDegree = n := by
  have hdegp : (monicOrtho s (n + 1)).natDegree = n + 1 := by
    have hd := monicOrtho_degree s (n + 1)
    rw [Polynomial.degree_eq_natDegree (monicOrtho_ne_zero s (n + 1))] at hd
    exact_mod_cast hd
  rw [lagrangeQuotient, natDegree_nodeCofactor, hdegp]
  omega

theorem eval_lagrangeQuotient_eq_zero (n : ℕ) {x₀ x : ℝ}
    (hx₀ : x₀ ∈ gaussNodes s n) (hx : x ∈ gaussNodes s n) (hne : x ≠ x₀) :
    (lagrangeQuotient s n x₀).eval x = 0 := by
  have hroot : (monicOrtho s (n + 1)).eval x₀ = 0 := (mem_gaussNodes_iff n x₀).1 hx₀
  have hmul := congrArg (fun q : Polynomial ℝ => q.eval x)
    (nodeCofactor_mul (monicOrtho s (n + 1)) hroot)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hmul
  have hrx : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).1 hx
  rw [hrx] at hmul
  have hsub : x - x₀ ≠ 0 := sub_ne_zero.2 hne
  rw [lagrangeQuotient]
  exact (mul_eq_zero.1 hmul).resolve_left hsub

theorem eval_lagrangeQuotient_self_ne_zero (h : PositiveMomentForm s) (n : ℕ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ gaussNodes s n) : (lagrangeQuotient s n x₀).eval x₀ ≠ 0 := by
  intro hzero
  have hroot : (monicOrtho s (n + 1)).eval x₀ = 0 := (mem_gaussNodes_iff n x₀).1 hx₀
  have hfac := nodeCofactor_mul (monicOrtho s (n + 1)) hroot
  have hdvd : ((Polynomial.X - Polynomial.C x₀) ^ (2 : ℕ) : Polynomial ℝ) ∣ monicOrtho s (n + 1) := by
    have hq : (Polynomial.X - Polynomial.C x₀) ∣ nodeCofactor (monicOrtho s (n + 1)) x₀ :=
      Polynomial.dvd_iff_isRoot.2 (by rw [lagrangeQuotient] at hzero; exact hzero)
    obtain ⟨g, hg⟩ := hq
    refine ⟨g, ?_⟩
    rw [← hfac, hg]
    ring
  exact monicOrtho_not_sq_dvd h n x₀ hdvd

/-- The energy of the Lagrange quotient at a node. -/
def lagrangeEnergy (s : ℕ → ℝ) (n : ℕ) (x₀ : ℝ) : ℝ :=
  momentFunctional s (lagrangeQuotient s n x₀ ^ (2 : ℕ))

theorem lagrangeEnergy_eq (h : PositiveMomentForm s) (n : ℕ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ gaussNodes s n) :
    lagrangeEnergy s n x₀ = christoffel s n x₀ * (lagrangeQuotient s n x₀).eval x₀ ^ (2 : ℕ) := by
  classical
  have hdeg : ((lagrangeQuotient s n x₀) ^ (2 : ℕ)).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have hnd : ((lagrangeQuotient s n x₀) ^ (2 : ℕ)).natDegree = 2 * n := by
      rw [Polynomial.natDegree_pow, natDegree_lagrangeQuotient]
    rw [hnd]
    exact_mod_cast Nat.lt_succ_of_le (by omega)
  rw [lagrangeEnergy, momentFunctional_eq_gaussSum h n _ hdeg]
  rw [Finset.sum_eq_single x₀]
  · rw [Polynomial.eval_pow]
  · intro x hx hne
    rw [Polynomial.eval_pow, eval_lagrangeQuotient_eq_zero n hx₀ hx hne]
    ring
  · intro hnot
    exact absurd hx₀ hnot

theorem lagrangeEnergy_pos (h : PositiveMomentForm s) (n : ℕ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ gaussNodes s n) : 0 < lagrangeEnergy s n x₀ := by
  rw [lagrangeEnergy_eq h n hx₀]
  have hpos := christoffel_pos h n x₀
  have hne := eval_lagrangeQuotient_self_ne_zero h n hx₀
  positivity

/-- **(SAHI.5) The endpoint signature of a single node.**  The Hausdorff-difference form of the
Lagrange quotient at a node is `1 - y x₀` times that quotient's own energy, so its sign is exactly
the position of the node relative to the moving apex `1/y`. -/
theorem hausdorffDifferenceForm_lagrangeQuotient (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ gaussNodes s n) :
    hausdorffDifferenceForm s y (lagrangeQuotient s n x₀)
      = (1 - y * x₀) * lagrangeEnergy s n x₀ := by
  classical
  rw [hausdorffDifferenceForm_eq_gaussSum h n y _ (le_of_eq (natDegree_lagrangeQuotient s n x₀)),
    lagrangeEnergy_eq h n hx₀]
  rw [Finset.sum_eq_single x₀]
  · ring
  · intro x hx hne
    rw [eval_lagrangeQuotient_eq_zero n hx₀ hx hne]
    ring
  · intro hnot
    exact absurd hx₀ hnot


/-! ## Super-apex detection -/

/-- **(SAHI.11) A node above the moving apex makes its own diagonal entry negative.** -/
theorem hausdorffDifferenceForm_lagrangeQuotient_neg (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ gaussNodes s n) (hsuper : 1 < y * x₀) :
    hausdorffDifferenceForm s y (lagrangeQuotient s n x₀) < 0 := by
  rw [hausdorffDifferenceForm_lagrangeQuotient h n y hx₀]
  have hpos := lagrangeEnergy_pos h n hx₀
  nlinarith

/-- A node below the moving apex makes its own diagonal entry positive. -/
theorem hausdorffDifferenceForm_lagrangeQuotient_pos (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ gaussNodes s n) (hsub : y * x₀ < 1) :
    0 < hausdorffDifferenceForm s y (lagrangeQuotient s n x₀) := by
  rw [hausdorffDifferenceForm_lagrangeQuotient h n y hx₀]
  have hpos := lagrangeEnergy_pos h n hx₀
  nlinarith

/-- **(SAHI.4) Without a super-apex node the Hausdorff-difference form is nonnegative.** -/
theorem hausdorffDifferenceForm_nonneg (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    (hall : ∀ x ∈ gaussNodes s n, y * x ≤ 1) (q : Polynomial ℝ) (hq : q.natDegree ≤ n) :
    0 ≤ hausdorffDifferenceForm s y q := by
  rw [hausdorffDifferenceForm_eq_gaussSum h n y q hq]
  refine Finset.sum_nonneg fun x hx => ?_
  have hw := (christoffel_pos h n x).le
  have hx1 : y * x ≤ 1 := hall x hx
  have hfac : 0 ≤ 1 - y * x := by linarith
  positivity

/-! ## The hard coordinate of a node -/

/-- The centered reciprocal hard coordinate of a node at mass `y`. -/
def hardCoordinate (y x : ℝ) : ℝ := x⁻¹ - y

/-- The normalized node coordinate. -/
def normalizedNode (y x : ℝ) : ℝ := y * x

/-- The Cayley coordinate of a node. -/
def cayleyNode (y x : ℝ) : ℝ := 2 * y * x - 1

/-- **(SAHI.10) The first-difference weight factors through the hard coordinate.** -/
theorem one_sub_mul_eq_mul_hardCoordinate (y x : ℝ) (hx : x ≠ 0) :
    1 - y * x = x * hardCoordinate y x := by
  rw [hardCoordinate]
  field_simp

/-- **(SAHI.9) The endpoint signature in the hard coordinate.** -/
theorem hausdorffDifferenceForm_lagrangeQuotient_hard (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ gaussNodes s n) (hx : x₀ ≠ 0) :
    hausdorffDifferenceForm s y (lagrangeQuotient s n x₀)
      = x₀ * hardCoordinate y x₀ * lagrangeEnergy s n x₀ := by
  rw [hausdorffDifferenceForm_lagrangeQuotient h n y hx₀, one_sub_mul_eq_mul_hardCoordinate y x₀ hx]

/-- **(SAHI.11) A negative hard coordinate is exactly a super-apex node.** -/
theorem hardCoordinate_neg_iff (y x : ℝ) (hx : 0 < x) :
    hardCoordinate y x < 0 ↔ 1 < normalizedNode y x := by
  rw [hardCoordinate, normalizedNode, sub_neg]
  have hxi : x⁻¹ * x = 1 := by field_simp
  constructor
  · intro hlt
    calc (1 : ℝ) = x⁻¹ * x := hxi.symm
      _ < y * x := mul_lt_mul_of_pos_right hlt hx
  · intro hlt
    have hmul : x⁻¹ * x < y * x := by
      rw [hxi]
      exact hlt
    exact lt_of_mul_lt_mul_right hmul hx.le

theorem add_hardCoordinate (y x : ℝ) : y + hardCoordinate y x = x⁻¹ := by
  rw [hardCoordinate]
  ring

/-- **(SAHI.12) The reciprocal boundary-layer scale of a node.** -/
theorem sub_inv_eq_hardCoordinate (y x : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) :
    x - y⁻¹ = -(hardCoordinate y x) / (y * (y + hardCoordinate y x)) := by
  rw [add_hardCoordinate, hardCoordinate]
  field_simp
  ring

/-- **(SAHI.13) The normalized boundary-layer scale.** -/
theorem normalizedNode_sub_one (y x : ℝ) (hx : x ≠ 0) :
    y * (normalizedNode y x - 1) = -(y * hardCoordinate y x) / (y + hardCoordinate y x) := by
  rw [add_hardCoordinate, normalizedNode, hardCoordinate]
  field_simp
  ring

/-- **(SAHI.13) The Cayley boundary-layer scale.** -/
theorem cayleyNode_sub_one (y x : ℝ) (hx : x ≠ 0) :
    y * (cayleyNode y x - 1) = -(2 * y * hardCoordinate y x) / (y + hardCoordinate y x) := by
  rw [add_hardCoordinate, cayleyNode, hardCoordinate]
  field_simp
  ring




/-- **(SAHI.8) The hard coordinate in the normalized variable.** -/
theorem hardCoordinate_eq_normalized (y x : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) :
    hardCoordinate y x = y * (1 - normalizedNode y x) / normalizedNode y x := by
  rw [hardCoordinate, normalizedNode]
  field_simp

/-- **(SAHI.27) The hard coordinate of an outlier just above the moving endpoint.** -/
theorem hardCoordinate_outlier (y c : ℝ) (hy : y ≠ 0) :
    y * (1 - (1 + c / y)) / (1 + c / y) = -c / (1 + c / y) := by
  have hnum : y * (1 - (1 + c / y)) = -c := by
    field_simp
    ring
  rw [hnum]

theorem tendsto_hardCoordinate_outlier (c : ℝ) :
    Filter.Tendsto (fun y : ℝ => -c / (1 + c / y)) Filter.atTop (nhds (-c)) := by
  have hquot : Filter.Tendsto (fun y : ℝ => c / y) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have hden : Filter.Tendsto (fun y : ℝ => 1 + c / y) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hquot
  have h : Filter.Tendsto (fun y : ℝ => (-c) / (1 + c / y)) Filter.atTop (nhds ((-c) / 1)) :=
    Filter.Tendsto.div tendsto_const_nhds hden one_ne_zero
  simpa using h


/-! ## Exact diagonalization on the Lagrange basis -/

theorem natDegree_lagrangeCombination_le (s : ℕ → ℝ) (n : ℕ) (c : ℝ → ℝ) :
    (∑ x ∈ gaussNodes s n, Polynomial.C (c x) * gaussBasis s n x).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_C, zero_add]
  have hd := gaussBasis_degree_lt s n x
  by_cases hz : gaussBasis s n x = 0
  · rw [hz, Polynomial.natDegree_zero]
    omega
  · rw [Polynomial.degree_eq_natDegree hz] at hd
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hd)

theorem eval_lagrangeCombination (h : PositiveMomentForm s) (n : ℕ) (c : ℝ → ℝ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ gaussNodes s n) :
    (∑ x ∈ gaussNodes s n, Polynomial.C (c x) * gaussBasis s n x).eval x₀ = c x₀ := by
  classical
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single x₀]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, gaussBasis_eval_self h n x₀, mul_one]
  · intro x hx hne
    have hxr : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).1 hx
    have hx₀r : (monicOrtho s (n + 1)).eval x₀ = 0 := (mem_gaussNodes_iff n x₀).1 hx₀
    rw [Polynomial.eval_mul, gaussBasis_eval_of_ne h n hxr hx₀r hne, mul_zero]
  · intro hnot
    exact absurd hx₀ hnot

/-- **(SAHI.4) Exact diagonalization of the Hausdorff-difference form.**  On the Lagrange basis of
the Gauss nodes the form is diagonal with entries `ω_i (1 - y x_i)`, so its inertia is exactly the
count of nodes below, at and above the moving apex `1/y`. -/
theorem hausdorffDifferenceForm_lagrangeCombination (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    (c : ℝ → ℝ) :
    hausdorffDifferenceForm s y (∑ x ∈ gaussNodes s n, Polynomial.C (c x) * gaussBasis s n x)
      = ∑ x ∈ gaussNodes s n, christoffel s n x * ((1 - y * x) * (c x) ^ (2 : ℕ)) := by
  rw [hausdorffDifferenceForm_eq_gaussSum h n y _ (natDegree_lagrangeCombination_le s n c)]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [eval_lagrangeCombination h n c hx]

/-! ## The finite node of a hard coordinate -/

/-- The finite quadrature node attached to a hard coordinate at mass `y`. -/
def hardNode (y u : ℝ) : ℝ := (y + u)⁻¹

theorem hardCoordinate_hardNode (y u : ℝ) :
    hardCoordinate y (hardNode y u) = u := by
  rw [hardCoordinate, hardNode, inv_inv]
  ring

theorem hardNode_pos {y u : ℝ} (hsum : 0 < y + u) : 0 < hardNode y u := by
  rw [hardNode]
  exact inv_pos.2 hsum

/-- **(SAHI §5) A negative hard coordinate is a super-apex node.**  If the hard coordinate is
negative and the shifted mass is still positive, the attached finite node lies strictly above the
moving apex `1/y`. -/
theorem normalizedNode_hardNode_gt_one {y u : ℝ} (hu : u < 0) (hsum : 0 < y + u) :
    1 < normalizedNode y (hardNode y u) := by
  rw [normalizedNode, hardNode]
  rw [lt_mul_inv_iff₀ hsum]
  linarith


/-- **(SAHI.6)/(SAHI.7) The hard substitution.**  The Cayley argument of the null polynomial at the
hard coordinate `u` is the reciprocal shifted mass. -/
theorem cayleyHardArgument (y u : ℝ) (hy : y ≠ 0) (hsum : y + u ≠ 0) :
    (1 + (1 - u / y) / (1 + u / y)) / (2 * y) = 1 / (y + u) := by
  have hden : 1 + u / y ≠ 0 := by
    intro hzero
    apply hsum
    field_simp at hzero
    linarith
  field_simp
  ring

/-- The Cayley coordinate of the finite node attached to a hard coordinate. -/
theorem cayleyNode_hardNode (y u : ℝ) (hy : y ≠ 0) (hsum : y + u ≠ 0) :
    cayleyNode y (hardNode y u) = (1 - u / y) / (1 + u / y) := by
  have hden : 1 + u / y ≠ 0 := by
    intro hzero
    apply hsum
    field_simp at hzero
    linarith
  rw [cayleyNode, hardNode]
  field_simp
  ring

/-! ## The first Hausdorff-difference matrix -/

theorem momentFunctional_C_mul_X_pow (s : ℕ → ℝ) (b : ℝ) (k : ℕ) :
    momentFunctional s (Polynomial.C b * Polynomial.X ^ k) = b * s k := by
  rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul, momentFunctional_X_pow]

theorem sq_sum_C_mul_X_pow {n : ℕ} (a : Fin n → ℝ) :
    (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) ^ (2 : ℕ)
      = ∑ i : Fin n, ∑ j : Fin n,
          Polynomial.C (a i * a j) * Polynomial.X ^ ((i : ℕ) + (j : ℕ)) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, pow_add]
  ring

/-- **(SAHI.17) The Hausdorff-difference form on a dilated polynomial is the quadratic form of the
first Hausdorff-difference matrix of the normalized moments.** -/
theorem hausdorffDifferenceForm_scaledPoly (s : ℕ → ℝ) (y : ℝ) {n : ℕ} (c : Fin n → ℝ) :
    hausdorffDifferenceForm s y
        (∑ i : Fin n, Polynomial.C (c i * y ^ (i : ℕ)) * Polynomial.X ^ (i : ℕ))
      = ∑ i : Fin n, ∑ j : Fin n, c i * c j *
          (y ^ ((i : ℕ) + (j : ℕ)) * s ((i : ℕ) + (j : ℕ))
            - y ^ ((i : ℕ) + (j : ℕ) + 1) * s ((i : ℕ) + (j : ℕ) + 1)) := by
  classical
  rw [hausdorffDifferenceForm, sq_sum_C_mul_X_pow]
  have hexpand : (1 - Polynomial.C y * Polynomial.X) *
      (∑ i : Fin n, ∑ j : Fin n,
        Polynomial.C (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ)))
          * Polynomial.X ^ ((i : ℕ) + (j : ℕ)))
      = ∑ i : Fin n, ∑ j : Fin n,
          (Polynomial.C (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ)))
              * Polynomial.X ^ ((i : ℕ) + (j : ℕ))
            - Polynomial.C (y * (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ))))
              * Polynomial.X ^ ((i : ℕ) + (j : ℕ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, pow_succ]
    ring
  rw [hexpand]
  rw [momentFunctional_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [momentFunctional_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : (Polynomial.C (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ)))
        * Polynomial.X ^ ((i : ℕ) + (j : ℕ))
      - Polynomial.C (y * (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ))))
        * Polynomial.X ^ ((i : ℕ) + (j : ℕ) + 1))
      = Polynomial.C (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ)))
          * Polynomial.X ^ ((i : ℕ) + (j : ℕ))
        + Polynomial.C (-(y * (c i * y ^ (i : ℕ) * (c j * y ^ (j : ℕ)))))
          * Polynomial.X ^ ((i : ℕ) + (j : ℕ) + 1) := by
    rw [map_neg]
    ring
  rw [hsub, momentFunctional_add, momentFunctional_C_mul_X_pow, momentFunctional_C_mul_X_pow,
    pow_add]
  ring


/-! ## Indefiniteness of the Hausdorff-difference matrix -/

theorem natDegree_scaledPoly_le {n : ℕ} (a : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
  omega

theorem exists_coeff_scaledPoly {y : ℝ} (hy : y ≠ 0) {n : ℕ} (q : Polynomial ℝ)
    (hq : q.natDegree ≤ n) :
    ∃ c : Fin (n + 1) → ℝ,
      (∑ i : Fin (n + 1), Polynomial.C (c i * y ^ (i : ℕ)) * Polynomial.X ^ (i : ℕ)) = q := by
  classical
  refine ⟨fun i => q.coeff (i : ℕ) / y ^ (i : ℕ), ?_⟩
  have hcoeff : ∀ i : Fin (n + 1),
      Polynomial.C (q.coeff (i : ℕ) / y ^ (i : ℕ) * y ^ (i : ℕ))
        = Polynomial.C (q.coeff (i : ℕ)) := by
    intro i
    congr 1
    field_simp
  simp only [hcoeff]
  rw [Fin.sum_univ_eq_sum_range fun i : ℕ => Polynomial.C (q.coeff i) * Polynomial.X ^ i]
  have hmon : ∀ i : ℕ, Polynomial.C (q.coeff i) * Polynomial.X ^ i
      = (Polynomial.monomial i) (q.coeff i) := by
    intro i
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  simp only [hmon]
  exact (Polynomial.as_sum_range' q (n + 1) (by omega)).symm

/-- **(SAHI.18) A super-apex node makes the first Hausdorff-difference matrix indefinite.** -/
theorem exists_neg_hausdorffDifferenceQuadratic (h : PositiveMomentForm s) (n : ℕ) {y : ℝ}
    (hy : y ≠ 0) {x₀ : ℝ} (hx₀ : x₀ ∈ gaussNodes s n) (hsuper : 1 < y * x₀) :
    ∃ c : Fin (n + 1) → ℝ,
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c i * c j *
        (y ^ ((i : ℕ) + (j : ℕ)) * s ((i : ℕ) + (j : ℕ))
          - y ^ ((i : ℕ) + (j : ℕ) + 1) * s ((i : ℕ) + (j : ℕ) + 1))) < 0 := by
  obtain ⟨c, hc⟩ := exists_coeff_scaledPoly hy (lagrangeQuotient s n x₀)
    (le_of_eq (natDegree_lagrangeQuotient s n x₀))
  refine ⟨c, ?_⟩
  rw [← hausdorffDifferenceForm_scaledPoly s y c, hc]
  exact hausdorffDifferenceForm_lagrangeQuotient_neg h n y hx₀ hsuper

/-- **(SAHI.19) Without a super-apex node the first Hausdorff-difference matrix is positive
semidefinite.** -/
theorem hausdorffDifferenceQuadratic_nonneg (h : PositiveMomentForm s) (n : ℕ) (y : ℝ)
    (hall : ∀ x ∈ gaussNodes s n, y * x ≤ 1) (c : Fin (n + 1) → ℝ) :
    0 ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c i * c j *
      (y ^ ((i : ℕ) + (j : ℕ)) * s ((i : ℕ) + (j : ℕ))
        - y ^ ((i : ℕ) + (j : ℕ) + 1) * s ((i : ℕ) + (j : ℕ) + 1)) := by
  rw [← hausdorffDifferenceForm_scaledPoly s y c]
  exact hausdorffDifferenceForm_nonneg h n y hall _
    (natDegree_scaledPoly_le fun i => c i * y ^ (i : ℕ))

end HTGeometry

end
