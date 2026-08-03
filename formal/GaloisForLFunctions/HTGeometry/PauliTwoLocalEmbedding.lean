import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels
import GaloisForLFunctions.HTGeometry.TwoLocalRealSliceGenericity

/-!
# The occupation form of a two-local Hamiltonian in Pauli coordinates

Occupation numbers and Pauli signs are affinely related, `occ = (1 - Z)/2`, so a Hamiltonian written
with one- and two-body occupation couplings and single-qubit flips is a combination of the identity,
the `Z` strings, the `Z Z` strings and the `X` strings.  Collecting the coefficients is a finite
rearrangement: the `i = j` interaction terms feed the identity and `Z_i` coefficients because
`occ^2 = occ`, and the two orientations of a pair feed the same `Z_i Z_j` label.

This dictionary embeds the two-local coefficients of the hypercube family into the coefficients of
any Pauli ensemble containing the strings of weight at most two.
-/

open scoped BigOperators Matrix.Norms.Elementwise
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Occupation numbers in terms of Pauli signs. -/
theorem boolOccupation_eq_zSign (b : Bool) :
    ((boolOccupation b : ℤ) : ℂ) = (1 - zSign b) / 2 := by
  cases b <;> simp [boolOccupation, zSign]

theorem boolOccupation_sq (b : Bool) :
    ((boolOccupation b : ℤ) : ℂ) * ((boolOccupation b : ℤ) : ℂ)
      = ((boolOccupation b : ℤ) : ℂ) := by
  cases b <;> simp [boolOccupation]

theorem boolOccupation_mul (a b : Bool) :
    ((boolOccupation a : ℤ) : ℂ) * ((boolOccupation b : ℤ) : ℂ)
      = (1 - zSign a - zSign b + zSign a * zSign b) / 4 := by
  rw [boolOccupation_eq_zSign, boolOccupation_eq_zSign]
  ring

theorem sum_sub_sub {α : Type*} (s : Finset α) (f g h : α → ℂ) :
    (∑ a ∈ s, (f a - g a - h a))
      = (∑ a ∈ s, f a) - (∑ a ∈ s, g a) - ∑ a ∈ s, h a := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

theorem sum_sub_sub_add {α : Type*} (s : Finset α) (f g h k : α → ℂ) :
    (∑ a ∈ s, (f a - g a - h a + k a))
      = (∑ a ∈ s, f a) - (∑ a ∈ s, g a) - (∑ a ∈ s, h a) + ∑ a ∈ s, k a := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- Swapping the two indices of a sum over ordered pairs of distinct indices. -/
theorem sum_erase_swap {M : Type*} [AddCommMonoid M] (f : Fin n → Fin n → M) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j)
      = ∑ i, ∑ j ∈ Finset.univ.erase i, f j i := by
  classical
  refine Finset.sum_comm' ?_
  intro x y
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Identity coefficient of the Pauli expansion. -/
def pauliIdentityCoefficient (v : HypercubeTwoLocalParameter n → ℂ) : ℂ :=
  v .constant +
    ((∑ i, (v (.onsite i) + v (.interaction i i)) / 2) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, v (.interaction i j) / 4)

/-- Single-qubit `Z` coefficients of the Pauli expansion. -/
def pauliZCoefficient (v : HypercubeTwoLocalParameter n → ℂ) (i : Fin n) : ℂ :=
  -((v (.onsite i) + v (.interaction i i)) / 2)
    - (∑ j ∈ Finset.univ.erase i, v (.interaction i j) / 4)
    - ∑ j ∈ Finset.univ.erase i, v (.interaction j i) / 4

/-- Pair `Z Z` coefficients of the Pauli expansion. -/
def pauliZZCoefficient (v : HypercubeTwoLocalParameter n → ℂ) (i j : Fin n) : ℂ :=
  v (.interaction i j) / 4

/-- **The diagonal dictionary.**  The occupation-form diagonal energy is the Pauli expansion of the
same Hamiltonian. -/
theorem hypercubeTwoLocalMatrix_diagonal_pauli (v : HypercubeTwoLocalParameter n → ℂ)
    (x : Fin n → Bool) :
    hypercubeTwoLocalMatrix v x x
      = pauliIdentityCoefficient v + (∑ i, pauliZCoefficient v i * zSign (x i))
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
            pauliZZCoefficient v i j * (zSign (x i) * zSign (x j)) := by
  classical
  set ζ : Fin n → ℂ := fun i => zSign (x i) with hζ
  set W : Fin n → ℂ := fun i => (v (.onsite i) + v (.interaction i i)) / 2 with hW
  set J : Fin n → Fin n → ℂ := fun i j => v (.interaction i j) / 4 with hJ
  have hleft : hypercubeTwoLocalMatrix v x x
      = v .constant + ((∑ i, (W i - W i * ζ i))
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
            (J i j - J i j * ζ i - J i j * ζ j + J i j * (ζ i * ζ j))) := by
    rw [hypercubeTwoLocalMatrix, hypercubeTwoLocalHamiltonian]
    simp only [if_true]
    rw [add_assoc]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hrow : (∑ j, v (.interaction i j) * ((boolOccupation (x i) : ℤ) : ℂ) *
          ((boolOccupation (x j) : ℤ) : ℂ))
        = v (.interaction i i) * ((boolOccupation (x i) : ℤ) : ℂ)
          + ∑ j ∈ Finset.univ.erase i, v (.interaction i j) *
            ((boolOccupation (x i) : ℤ) : ℂ) * ((boolOccupation (x j) : ℤ) : ℂ) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      rw [mul_assoc, boolOccupation_sq]
    rw [hrow]
    have hpair : ∀ j ∈ Finset.univ.erase i,
        v (.interaction i j) * ((boolOccupation (x i) : ℤ) : ℂ) *
            ((boolOccupation (x j) : ℤ) : ℂ)
          = J i j - J i j * ζ i - J i j * ζ j + J i j * (ζ i * ζ j) := by
      intro j _
      rw [mul_assoc, boolOccupation_mul, hJ, hζ]
      ring
    rw [Finset.sum_congr rfl hpair]
    rw [boolOccupation_eq_zSign, hW, hζ]
    ring
  rw [hleft]
  have hLsplit : (∑ i, (W i - W i * ζ i)) = (∑ i, W i) - ∑ i, W i * ζ i :=
    Finset.sum_sub_distrib _ _
  have hRsplit : (∑ i, ∑ j ∈ Finset.univ.erase i,
        (J i j - J i j * ζ i - J i j * ζ j + J i j * (ζ i * ζ j)))
      = (∑ i, ∑ j ∈ Finset.univ.erase i, J i j)
        - (∑ i, ∑ j ∈ Finset.univ.erase i, J i j * ζ i)
        - (∑ i, ∑ j ∈ Finset.univ.erase i, J i j * ζ j)
        + ∑ i, ∑ j ∈ Finset.univ.erase i, J i j * (ζ i * ζ j) := by
    rw [← sum_sub_sub_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_sub_sub_add]
  have hident : pauliIdentityCoefficient v
      = v .constant + ((∑ i, W i) + ∑ i, ∑ j ∈ Finset.univ.erase i, J i j) := rfl
  have hz : (∑ i, pauliZCoefficient v i * ζ i)
      = -(∑ i, W i * ζ i)
        - (∑ i, ∑ j ∈ Finset.univ.erase i, J i j * ζ i)
        - ∑ i, ∑ j ∈ Finset.univ.erase i, J i j * ζ j := by
    have hterm : ∀ i : Fin n, pauliZCoefficient v i * ζ i
        = -(W i * ζ i) - (∑ j ∈ Finset.univ.erase i, J i j * ζ i)
          - ∑ j ∈ Finset.univ.erase i, J j i * ζ i := by
      intro i
      rw [pauliZCoefficient, sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul, neg_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, sum_sub_sub, Finset.sum_neg_distrib]
    congr 1
    exact (sum_erase_swap fun i j => J i j * ζ j).symm
  have hzz : (∑ i, ∑ j ∈ Finset.univ.erase i,
        pauliZZCoefficient v i j * (zSign (x i) * zSign (x j)))
      = ∑ i, ∑ j ∈ Finset.univ.erase i, J i j * (ζ i * ζ j) := rfl
  rw [hident, hz, hzz, hLsplit, hRsplit]
  abel


/-! ## The bounded-weight Pauli family -/

/-- Pauli strings of weight at most `q`. -/
abbrev PauliBoundedLabel (n q : ℕ) : Type := {P : Fin n → Option (Fin 3) // pauliWeight P ≤ q}

/-- The polynomial matrix family of all Pauli strings of weight at most `q`. -/
def pauliBoundedPolynomialMatrix (n q : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool) (MvPolynomial (PauliBoundedLabel n q) ℂ) :=
  fun x y => ∑ P : PauliBoundedLabel n q,
    MvPolynomial.X P * MvPolynomial.C (finitePauliMatrix P.1 x y)

theorem eval_pauliBoundedPolynomialMatrix {q : ℕ} (z : PauliBoundedLabel n q → ℂ)
    (x y : Fin n → Bool) :
    ((pauliBoundedPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z)) x y
      = ∑ P : PauliBoundedLabel n q, z P * finitePauliMatrix P.1 x y := by
  simp [pauliBoundedPolynomialMatrix, Matrix.map_apply]

/-- Only the prescribed label contributes to a label-indexed selection sum. -/
theorem sum_ite_label_mul {q : ℕ} {L : Fin n → Option (Fin 3)} (hL : pauliWeight L ≤ q) (c : ℂ)
    (f : (Fin n → Option (Fin 3)) → ℂ) :
    (∑ P : PauliBoundedLabel n q, (if P.1 = L then c else 0) * f P.1) = c * f L := by
  classical
  rw [Finset.sum_eq_single (⟨L, hL⟩ : PauliBoundedLabel n q)]
  · rw [if_pos rfl]
  · intro P _ hP
    rw [if_neg fun hcon => hP (Subtype.ext hcon), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (⟨L, hL⟩ : PauliBoundedLabel n q)) h

/-- A finite family of label selections collapses to the family sum. -/
theorem sum_ite_family_mul {q : ℕ} {ι : Type*} [Fintype ι]
    (lab : ι → (Fin n → Option (Fin 3))) (hlab : ∀ a, pauliWeight (lab a) ≤ q)
    (c : ι → ℂ) (f : (Fin n → Option (Fin 3)) → ℂ) :
    (∑ P : PauliBoundedLabel n q, (∑ a, if P.1 = lab a then c a else 0) * f P.1)
      = ∑ a, c a * f (lab a) := by
  have hstep : ∀ P : PauliBoundedLabel n q,
      (∑ a, if P.1 = lab a then c a else 0) * f P.1
        = ∑ a, (if P.1 = lab a then c a else 0) * f P.1 :=
    fun P => Finset.sum_mul _ _ _
  rw [Finset.sum_congr rfl fun P _ => hstep P, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => sum_ite_label_mul (hlab a) _ _

/-- The Pauli coefficients of an occupation-form two-local Hamiltonian. -/
def pauliBoundedCoefficient {q : ℕ} (v : HypercubeTwoLocalParameter n → ℂ) :
    PauliBoundedLabel n q → ℂ := fun P =>
  (if P.1 = pauliIdentityLabel n then pauliIdentityCoefficient v else 0)
    + (∑ i, if P.1 = pauliZLabel i then pauliZCoefficient v i else 0)
    + (∑ ij : Fin n × Fin n, if P.1 = pauliZZLabel ij.1 ij.2 then
        (if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2) else 0)
    + ∑ i, if P.1 = pauliXLabel i then v (.transverse i) else 0

/-- **The Pauli embedding of the hypercube two-local family.**  The occupation-form two-local
Hamiltonian is the Pauli combination of the identity, the `Z`, the `Z Z` and the `X` strings with
the coefficients read off from the occupation couplings. -/
theorem eval_pauliBoundedCoefficient_eq_hypercubeTwoLocalMatrix {q : ℕ} (hq : 2 ≤ q)
    (v : HypercubeTwoLocalParameter n → ℂ) :
    (pauliBoundedPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (pauliBoundedCoefficient v))
      = hypercubeTwoLocalMatrix v := by
  have hone : (1 : ℕ) ≤ q := le_trans (by norm_num) hq
  have hIw : pauliWeight (pauliIdentityLabel n) ≤ q := by
    rw [pauliWeight_pauliIdentityLabel]
    exact Nat.zero_le q
  have hZw : ∀ i : Fin n, pauliWeight (pauliZLabel i) ≤ q := by
    intro i
    rw [pauliWeight_pauliZLabel]
    exact hone
  have hXw : ∀ i : Fin n, pauliWeight (pauliXLabel i) ≤ q := by
    intro i
    rw [pauliWeight_pauliXLabel]
    exact hone
  have hZZw : ∀ ij : Fin n × Fin n, pauliWeight (pauliZZLabel ij.1 ij.2) ≤ q :=
    fun ij => le_trans (pauliWeight_pauliZZLabel_le ij.1 ij.2) hq
  ext x y
  rw [eval_pauliBoundedPolynomialMatrix]
  have hsplit : (∑ P : PauliBoundedLabel n q,
        pauliBoundedCoefficient v P * finitePauliMatrix P.1 x y)
      = (∑ P : PauliBoundedLabel n q,
          (if P.1 = pauliIdentityLabel n then pauliIdentityCoefficient v else 0) *
            finitePauliMatrix P.1 x y)
        + (∑ P : PauliBoundedLabel n q,
            (∑ i, if P.1 = pauliZLabel i then pauliZCoefficient v i else 0) *
              finitePauliMatrix P.1 x y)
        + (∑ P : PauliBoundedLabel n q,
            (∑ ij : Fin n × Fin n, if P.1 = pauliZZLabel ij.1 ij.2 then
              (if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2) else 0) *
              finitePauliMatrix P.1 x y)
        + ∑ P : PauliBoundedLabel n q,
            (∑ i, if P.1 = pauliXLabel i then v (.transverse i) else 0) *
              finitePauliMatrix P.1 x y := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [pauliBoundedCoefficient]
    ring
  rw [hsplit,
    sum_ite_label_mul hIw (pauliIdentityCoefficient v) (fun L => finitePauliMatrix L x y),
    sum_ite_family_mul pauliZLabel hZw (pauliZCoefficient v)
      (fun L => finitePauliMatrix L x y),
    sum_ite_family_mul (fun ij : Fin n × Fin n => pauliZZLabel ij.1 ij.2) hZZw
      (fun ij : Fin n × Fin n =>
        if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2)
      (fun L => finitePauliMatrix L x y),
    sum_ite_family_mul pauliXLabel hXw (fun i => v (.transverse i))
      (fun L => finitePauliMatrix L x y)]
  have hZZpairs : (∑ ij : Fin n × Fin n,
      (if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2) *
        finitePauliMatrix (pauliZZLabel ij.1 ij.2) x y)
      = ∑ i, ∑ j ∈ Finset.univ.erase i,
          pauliZZCoefficient v i j * finitePauliMatrix (pauliZZLabel i j) x y := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
  rw [hZZpairs]
  by_cases hxy : x = y
  · subst hxy
    have hI : finitePauliMatrix (pauliIdentityLabel n) x x = 1 := by
      rw [finitePauliMatrix_pauliIdentityLabel, if_pos rfl]
    have hZ : ∀ i : Fin n, pauliZCoefficient v i * finitePauliMatrix (pauliZLabel i) x x
        = pauliZCoefficient v i * zSign (x i) := by
      intro i
      rw [finitePauliMatrix_pauliZLabel, if_pos rfl]
    have hX : ∀ i : Fin n, v (.transverse i) * finitePauliMatrix (pauliXLabel i) x x = 0 := by
      intro i
      rw [finitePauliMatrix_pauliXLabel, if_neg (boolToggle_ne x i), mul_zero]
    have hZZ : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
        pauliZZCoefficient v i j * finitePauliMatrix (pauliZZLabel i j) x x
          = pauliZZCoefficient v i j * (zSign (x i) * zSign (x j)) := by
      intro i j hj
      rw [finitePauliMatrix_pauliZZLabel (Ne.symm (Finset.mem_erase.mp hj).1), if_pos rfl]
    rw [hI, mul_one, Finset.sum_congr rfl fun i _ => hZ i,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (hZZ i),
      Finset.sum_congr rfl fun i _ => hX i, Finset.sum_const_zero, add_zero]
    exact (hypercubeTwoLocalMatrix_diagonal_pauli v x).symm
  · have hI : finitePauliMatrix (pauliIdentityLabel n) x y = 0 := by
      rw [finitePauliMatrix_pauliIdentityLabel, if_neg hxy]
    have hZ : ∀ i : Fin n, pauliZCoefficient v i * finitePauliMatrix (pauliZLabel i) x y = 0 := by
      intro i
      rw [finitePauliMatrix_pauliZLabel, if_neg hxy, mul_zero]
    have hZZ : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
        pauliZZCoefficient v i j * finitePauliMatrix (pauliZZLabel i j) x y = 0 := by
      intro i j hj
      rw [finitePauliMatrix_pauliZZLabel (Ne.symm (Finset.mem_erase.mp hj).1), if_neg hxy,
        mul_zero]
    rw [hI, mul_zero, Finset.sum_congr rfl fun i _ => hZ i, Finset.sum_const_zero,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (hZZ i)]
    simp only [Finset.sum_const_zero, add_zero, zero_add]
    rw [hypercubeTwoLocalMatrix, hypercubeTwoLocalHamiltonian, if_neg hxy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finitePauliMatrix_pauliXLabel]
    by_cases hy : y = boolToggle x i
    · rw [if_pos hy, if_pos hy, mul_one]
    · rw [if_neg hy, if_neg hy, mul_zero]


/-! ## Numbered coefficients and the genericity conclusion -/

/-- Numbering of the Pauli labels of weight at most `q`. -/
def pauliBoundedLabelEquivFin (n q : ℕ) :
    PauliBoundedLabel n q ≃ Fin (Fintype.card (PauliBoundedLabel n q)) :=
  Fintype.equivFin _

/-- The bounded-weight Pauli family in numbered coefficients. -/
def pauliBoundedFinPolynomialMatrix (n q : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool)
      (MvPolynomial (Fin (Fintype.card (PauliBoundedLabel n q))) ℂ) :=
  (pauliBoundedPolynomialMatrix n q).map (MvPolynomial.rename (pauliBoundedLabelEquivFin n q))

theorem map_eval_pauliBoundedFinPolynomialMatrix {q : ℕ}
    (z : Fin (Fintype.card (PauliBoundedLabel n q)) → ℂ) :
    (pauliBoundedFinPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z)
      = (pauliBoundedPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun P => z (pauliBoundedLabelEquivFin n q P)) := by
  rw [pauliBoundedFinPolynomialMatrix, Matrix.map_map]
  have hcomp : (⇑(MvPolynomial.eval₂Hom (RingHom.id ℂ) z) ∘
        ⇑(MvPolynomial.rename (pauliBoundedLabelEquivFin n q)))
      = ⇑(MvPolynomial.eval₂Hom (RingHom.id ℂ)
        fun P => z (pauliBoundedLabelEquivFin n q P)) := by
    funext p
    show MvPolynomial.eval₂ (RingHom.id ℂ) z
        ((MvPolynomial.rename (pauliBoundedLabelEquivFin n q)) p) = _
    rw [MvPolynomial.eval₂_rename]
    rfl
  rw [hcomp]

/-- The numbered Pauli coefficients of an occupation-form two-local Hamiltonian. -/
def pauliBoundedFinCoefficient {q : ℕ} (v : HypercubeTwoLocalParameter n → ℂ) :
    Fin (Fintype.card (PauliBoundedLabel n q)) → ℂ :=
  fun t => pauliBoundedCoefficient v ((pauliBoundedLabelEquivFin n q).symm t)

theorem map_eval_pauliBoundedFinCoefficient {q : ℕ} (hq : 2 ≤ q)
    (v : HypercubeTwoLocalParameter n → ℂ) :
    (pauliBoundedFinPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (pauliBoundedFinCoefficient v))
      = hypercubeTwoLocalMatrix v := by
  rw [map_eval_pauliBoundedFinPolynomialMatrix]
  have hcoeff : (fun P => pauliBoundedFinCoefficient (q := q) v
      (pauliBoundedLabelEquivFin n q P)) = pauliBoundedCoefficient v := by
    funext P
    simp [pauliBoundedFinCoefficient]
  rw [hcoeff]
  exact eval_pauliBoundedCoefficient_eq_hypercubeTwoLocalMatrix hq v

/-- A selection whose condition does not depend on the parameter is continuous. -/
theorem continuous_ite_const {E : Type*} [TopologicalSpace E] (c : Prop) [Decidable c]
    {g : E → ℂ} (hg : Continuous g) : Continuous fun v => if c then g v else 0 := by
  by_cases hc : c
  · simpa [hc] using hg
  · simpa [hc] using continuous_const

theorem continuous_coordinate (θ : HypercubeTwoLocalParameter n) :
    Continuous fun v : HypercubeTwoLocalParameter n → ℂ => v θ := continuous_apply θ

theorem continuous_pauliIdentityCoefficient :
    Continuous (pauliIdentityCoefficient (n := n)) := by
  unfold pauliIdentityCoefficient
  fun_prop

theorem continuous_pauliZCoefficient (i : Fin n) :
    Continuous fun v : HypercubeTwoLocalParameter n → ℂ => pauliZCoefficient v i := by
  unfold pauliZCoefficient
  fun_prop

theorem continuous_pauliZZCoefficient (i j : Fin n) :
    Continuous fun v : HypercubeTwoLocalParameter n → ℂ => pauliZZCoefficient v i j := by
  unfold pauliZZCoefficient
  fun_prop

theorem continuous_pauliBoundedFinCoefficient {q : ℕ} :
    Continuous (pauliBoundedFinCoefficient (n := n) (q := q)) := by
  refine continuous_pi fun t => ?_
  unfold pauliBoundedFinCoefficient pauliBoundedCoefficient
  refine (((continuous_ite_const _ continuous_pauliIdentityCoefficient).add ?_).add ?_).add ?_
  · exact continuous_finsetSum _ fun i _ =>
      continuous_ite_const _ (continuous_pauliZCoefficient i)
  · refine continuous_finsetSum _ fun ij _ => ?_
    refine continuous_ite_const _ ?_
    by_cases hij : ij.1 = ij.2
    · simpa [hij] using continuous_const
    · simpa [hij] using continuous_pauliZZCoefficient ij.1 ij.2
  · exact continuous_finsetSum _ fun i _ =>
      continuous_ite_const _ (continuous_coordinate _)

/-- **Real-slice genericity of every fixed-weight Pauli ensemble.**  For `q >= 2`, outside a meagre
Lebesgue-null set of real coefficients of the Pauli strings of weight at most `q`, the `2^n`
energies satisfy no nonzero balanced integer relation. -/
theorem pauliBoundedFin_dense_residual_fullMeasure (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Dense (polynomialMatrixProjectiveGenericSet (pauliBoundedFinPolynomialMatrix n q)) ∧
      polynomialMatrixProjectiveGenericSet (pauliBoundedFinPolynomialMatrix n q) ∈
        residual (Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (pauliBoundedFinPolynomialMatrix n q))ᶜ = 0 :=
  polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_twoLocalEmbedding
    (pauliBoundedFinPolynomialMatrix n q) pauliBoundedFinCoefficient (fun _ => 0)
    continuous_pauliBoundedFinCoefficient
    (fun p => by
      rw [show (((0 : ℝ) : ℂ)) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 by simp,
        sub_zero]
      exact map_eval_pauliBoundedFinCoefficient hq fun θ => (p θ : ℂ))
    (fun p i q' => by
      rw [show (((0 : ℝ) : ℂ)) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 by simp,
        sub_zero]
      exact map_eval_pauliBoundedFinCoefficient hq (twoLocalEdgeSlice p i q'))

/-- At real coefficients a Pauli combination is Hermitian. -/
theorem isHermitian_pauliBoundedFinEval {q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) :
    ((pauliBoundedFinPolynomialMatrix n q).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (p t : ℂ))).IsHermitian := by
  rw [map_eval_pauliBoundedFinPolynomialMatrix]
  refine Matrix.IsHermitian.ext fun x y => ?_
  rw [eval_pauliBoundedPolynomialMatrix, eval_pauliBoundedPolynomialMatrix, star_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [star_mul']
  have hstar : star (finitePauliMatrix P.1 y x) = finitePauliMatrix P.1 x y := by
    have h := finitePauliMatrix_isHermitian P.1
    rw [Matrix.IsHermitian] at h
    exact congrFun (congrFun h x) y
  rw [hstar]
  congr 1
  exact Complex.conj_ofReal _

/-- **Two-local spectral genericity in Pauli coordinates.**  For `q >= 2`, almost every real
combination of Pauli strings of weight at most `q` has pairwise distinct energies admitting no
balanced integer relation. -/
theorem pauliBounded_simple_and_projectivelyIndependent_generically (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Dense (polynomialMatrixProjectiveGenericSet (pauliBoundedFinPolynomialMatrix n q)) ∧
      polynomialMatrixProjectiveGenericSet (pauliBoundedFinPolynomialMatrix n q) ∈
        residual (Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (pauliBoundedFinPolynomialMatrix n q))ᶜ = 0 ∧
      ∀ p ∈ polynomialMatrixProjectiveGenericSet (pauliBoundedFinPolynomialMatrix n q),
        Function.Injective (isHermitian_pauliBoundedFinEval p).eigenvalues ∧
        MaximallyProjectiveEnergy (isHermitian_pauliBoundedFinEval p).eigenvalues := by
  obtain ⟨hdense, hresidual, hvolume⟩ := pauliBoundedFin_dense_residual_fullMeasure n hq
  refine ⟨hdense, hresidual, hvolume, fun p hp => ⟨?_, ?_⟩⟩
  · exact MaximallyProjectiveEnergy.injective
      (maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ p hp _)
  · exact maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ p hp _

/-- **Almost sure spectral genericity for any absolutely continuous Pauli ensemble.** -/
theorem pauliBounded_projectivelyIndependent_ae (n : ℕ) {q : ℕ} (hq : 2 ≤ q)
    {μ : Measure (Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)} (hμ : μ ≪ volume) :
    ∀ᵐ p ∂μ, Function.Injective (isHermitian_pauliBoundedFinEval p).eigenvalues ∧
      MaximallyProjectiveEnergy (isHermitian_pauliBoundedFinEval p).eigenvalues := by
  obtain ⟨-, -, hvolume, hgeneric⟩ :=
    pauliBounded_simple_and_projectivelyIndependent_generically n hq
  refine MeasureTheory.measure_mono_null (fun z hz => ?_) (hμ hvolume)
  by_contra hcon
  exact hz (hgeneric z (by simpa using hcon))


/-! ## The traceless ensemble -/

theorem pauliZLabel_ne_identity (i : Fin n) : pauliZLabel i ≠ pauliIdentityLabel n := by
  intro h
  have hi := congrFun h i
  simp [pauliZLabel, pauliIdentityLabel] at hi

theorem pauliZZLabel_ne_identity (i j : Fin n) : pauliZZLabel i j ≠ pauliIdentityLabel n := by
  intro h
  have hi := congrFun h i
  simp [pauliZZLabel, pauliIdentityLabel] at hi

theorem pauliXLabel_ne_identity (i : Fin n) : pauliXLabel i ≠ pauliIdentityLabel n := by
  intro h
  have hi := congrFun h i
  simp [pauliXLabel, pauliIdentityLabel] at hi

/-- Nonidentity Pauli strings of weight at most `q`. -/
abbrev PauliTracelessLabel (n q : ℕ) : Type :=
  {P : Fin n → Option (Fin 3) // pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n}

/-- The polynomial matrix family of the nonidentity Pauli strings of weight at most `q`. -/
def pauliTracelessPolynomialMatrix (n q : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool) (MvPolynomial (PauliTracelessLabel n q) ℂ) :=
  fun x y => ∑ P : PauliTracelessLabel n q,
    MvPolynomial.X P * MvPolynomial.C (finitePauliMatrix P.1 x y)

theorem eval_pauliTracelessPolynomialMatrix {q : ℕ} (z : PauliTracelessLabel n q → ℂ)
    (x y : Fin n → Bool) :
    ((pauliTracelessPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z)) x y
      = ∑ P : PauliTracelessLabel n q, z P * finitePauliMatrix P.1 x y := by
  simp [pauliTracelessPolynomialMatrix, Matrix.map_apply]

/-- Only the prescribed label contributes to a label-indexed selection sum. -/
theorem sum_ite_target_mul {L : Type*} [Fintype L] [DecidableEq L]
    (lab : L → (Fin n → Option (Fin 3))) (hlab : Function.Injective lab)
    {T : Fin n → Option (Fin 3)} {L₀ : L} (hL₀ : lab L₀ = T) (c : ℂ)
    (f : (Fin n → Option (Fin 3)) → ℂ) :
    (∑ P : L, (if lab P = T then c else 0) * f (lab P)) = c * f T := by
  classical
  rw [Finset.sum_eq_single L₀]
  · rw [hL₀, if_pos rfl]
  · intro P _ hP
    rw [if_neg fun hcon => hP (hlab (hcon.trans hL₀.symm)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ L₀) h

/-- A finite family of label selections collapses to the family sum. -/
theorem sum_ite_family_target_mul {L ι : Type*} [Fintype L] [DecidableEq L] [Fintype ι]
    (lab : L → (Fin n → Option (Fin 3))) (hlab : Function.Injective lab)
    (target : ι → (Fin n → Option (Fin 3))) (hmem : ∀ a, ∃ L₀ : L, lab L₀ = target a)
    (c : ι → ℂ) (f : (Fin n → Option (Fin 3)) → ℂ) :
    (∑ P : L, (∑ a, if lab P = target a then c a else 0) * f (lab P))
      = ∑ a, c a * f (target a) := by
  have hstep : ∀ P : L, (∑ a, if lab P = target a then c a else 0) * f (lab P)
      = ∑ a, (if lab P = target a then c a else 0) * f (lab P) :=
    fun P => Finset.sum_mul _ _ _
  rw [Finset.sum_congr rfl fun P _ => hstep P, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨L₀, hL₀⟩ := hmem a
  exact sum_ite_target_mul lab hlab hL₀ (c a) f

/-- The nonidentity Pauli coefficients of an occupation-form two-local Hamiltonian. -/
def pauliTracelessCoefficient {q : ℕ} (v : HypercubeTwoLocalParameter n → ℂ) :
    PauliTracelessLabel n q → ℂ := fun P =>
  (∑ i, if P.1 = pauliZLabel i then pauliZCoefficient v i else 0)
    + (∑ ij : Fin n × Fin n, if P.1 = pauliZZLabel ij.1 ij.2 then
        (if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2) else 0)
    + ∑ i, if P.1 = pauliXLabel i then v (.transverse i) else 0

/-- **The traceless Pauli embedding.**  Dropping the identity string leaves the two-local
Hamiltonian minus its mean energy. -/
theorem eval_pauliTracelessCoefficient {q : ℕ} (hq : 2 ≤ q)
    (v : HypercubeTwoLocalParameter n → ℂ) :
    (pauliTracelessPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (pauliTracelessCoefficient v))
      = hypercubeTwoLocalMatrix v
        - (pauliIdentityCoefficient v) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  have hone : (1 : ℕ) ≤ q := le_trans (by norm_num) hq
  have hlab : Function.Injective (Subtype.val :
      PauliTracelessLabel n q → (Fin n → Option (Fin 3))) := Subtype.val_injective
  have hZmem : ∀ i : Fin n, ∃ L : PauliTracelessLabel n q, L.1 = pauliZLabel i := fun i =>
    ⟨⟨pauliZLabel i, ⟨by rw [pauliWeight_pauliZLabel]; exact hone, pauliZLabel_ne_identity i⟩⟩,
      rfl⟩
  have hXmem : ∀ i : Fin n, ∃ L : PauliTracelessLabel n q, L.1 = pauliXLabel i := fun i =>
    ⟨⟨pauliXLabel i, ⟨by rw [pauliWeight_pauliXLabel]; exact hone, pauliXLabel_ne_identity i⟩⟩,
      rfl⟩
  have hZZmem : ∀ ij : Fin n × Fin n,
      ∃ L : PauliTracelessLabel n q, L.1 = pauliZZLabel ij.1 ij.2 := fun ij =>
    ⟨⟨pauliZZLabel ij.1 ij.2, ⟨le_trans (pauliWeight_pauliZZLabel_le ij.1 ij.2) hq,
      pauliZZLabel_ne_identity ij.1 ij.2⟩⟩, rfl⟩
  ext x y
  rw [eval_pauliTracelessPolynomialMatrix]
  have hsplit : (∑ P : PauliTracelessLabel n q,
        pauliTracelessCoefficient v P * finitePauliMatrix P.1 x y)
      = (∑ P : PauliTracelessLabel n q,
          (∑ i, if P.1 = pauliZLabel i then pauliZCoefficient v i else 0) *
            finitePauliMatrix P.1 x y)
        + (∑ P : PauliTracelessLabel n q,
            (∑ ij : Fin n × Fin n, if P.1 = pauliZZLabel ij.1 ij.2 then
              (if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2) else 0) *
              finitePauliMatrix P.1 x y)
        + ∑ P : PauliTracelessLabel n q,
            (∑ i, if P.1 = pauliXLabel i then v (.transverse i) else 0) *
              finitePauliMatrix P.1 x y := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [pauliTracelessCoefficient]
    ring
  rw [hsplit,
    sum_ite_family_target_mul Subtype.val hlab pauliZLabel hZmem (pauliZCoefficient v)
      (fun L => finitePauliMatrix L x y),
    sum_ite_family_target_mul Subtype.val hlab
      (fun ij : Fin n × Fin n => pauliZZLabel ij.1 ij.2) hZZmem
      (fun ij : Fin n × Fin n =>
        if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2)
      (fun L => finitePauliMatrix L x y),
    sum_ite_family_target_mul Subtype.val hlab pauliXLabel hXmem
      (fun i => v (.transverse i)) (fun L => finitePauliMatrix L x y)]
  have hZZpairs : (∑ ij : Fin n × Fin n,
      (if ij.1 = ij.2 then 0 else pauliZZCoefficient v ij.1 ij.2) *
        finitePauliMatrix (pauliZZLabel ij.1 ij.2) x y)
      = ∑ i, ∑ j ∈ Finset.univ.erase i,
          pauliZZCoefficient v i j * finitePauliMatrix (pauliZZLabel i j) x y := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
  rw [hZZpairs]
  by_cases hxy : x = y
  · subst hxy
    have hZ : ∀ i : Fin n, pauliZCoefficient v i * finitePauliMatrix (pauliZLabel i) x x
        = pauliZCoefficient v i * zSign (x i) := by
      intro i
      rw [finitePauliMatrix_pauliZLabel, if_pos rfl]
    have hX : ∀ i : Fin n, v (.transverse i) * finitePauliMatrix (pauliXLabel i) x x = 0 := by
      intro i
      rw [finitePauliMatrix_pauliXLabel, if_neg (boolToggle_ne x i), mul_zero]
    have hZZ : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
        pauliZZCoefficient v i j * finitePauliMatrix (pauliZZLabel i j) x x
          = pauliZZCoefficient v i j * (zSign (x i) * zSign (x j)) := by
      intro i j hj
      rw [finitePauliMatrix_pauliZZLabel (Ne.symm (Finset.mem_erase.mp hj).1), if_pos rfl]
    rw [Finset.sum_congr rfl fun i _ => hZ i,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (hZZ i),
      Finset.sum_congr rfl fun i _ => hX i, Finset.sum_const_zero, add_zero]
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one,
      hypercubeTwoLocalMatrix_diagonal_pauli v x]
    ring
  · have hZ : ∀ i : Fin n, pauliZCoefficient v i * finitePauliMatrix (pauliZLabel i) x y = 0 := by
      intro i
      rw [finitePauliMatrix_pauliZLabel, if_neg hxy, mul_zero]
    have hZZ : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
        pauliZZCoefficient v i j * finitePauliMatrix (pauliZZLabel i j) x y = 0 := by
      intro i j hj
      rw [finitePauliMatrix_pauliZZLabel (Ne.symm (Finset.mem_erase.mp hj).1), if_neg hxy,
        mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hZ i, Finset.sum_const_zero,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (hZZ i)]
    simp only [Finset.sum_const_zero, add_zero, zero_add]
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hxy, mul_zero,
      sub_zero, hypercubeTwoLocalMatrix, hypercubeTwoLocalHamiltonian, if_neg hxy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finitePauliMatrix_pauliXLabel]
    by_cases hy : y = boolToggle x i
    · rw [if_pos hy, if_pos hy, mul_one]
    · rw [if_neg hy, if_neg hy, mul_zero]


/-- The identity Pauli coefficient of a real two-local coefficient vector. -/
def pauliIdentityRealCoefficient (p : HypercubeTwoLocalParameter n → ℝ) : ℝ :=
  p .constant + ((∑ i, (p (.onsite i) + p (.interaction i i)) / 2)
    + ∑ i, ∑ j ∈ Finset.univ.erase i, p (.interaction i j) / 4)

theorem pauliIdentityCoefficient_ofReal (p : HypercubeTwoLocalParameter n → ℝ) :
    pauliIdentityCoefficient (fun θ => (p θ : ℂ))
      = ((pauliIdentityRealCoefficient p : ℝ) : ℂ) := by
  rw [pauliIdentityCoefficient, pauliIdentityRealCoefficient]
  push_cast
  ring

/-- **The identity coefficient is a gauge along the edge slice.**  The slice moves the constant term
by `t` and one onsite term by `-2t`, which the identity coefficient weights by `1` and `1/2`. -/
theorem pauliIdentityRealCoefficient_edgeShift (p : HypercubeTwoLocalParameter n → ℝ)
    (i : Fin n) (t : ℝ) :
    pauliIdentityRealCoefficient (p + t • edgeShiftDirection i)
      = pauliIdentityRealCoefficient p := by
  classical
  have hconst : (p + t • edgeShiftDirection i) HypercubeTwoLocalParameter.constant
      = p HypercubeTwoLocalParameter.constant + t := by
    simp [edgeShiftDirection_constant]
  have honsite : ∀ j : Fin n, (p + t • edgeShiftDirection i) (.onsite j)
      = p (.onsite j) + t * (if j = i then -2 else 0) := by
    intro j
    simp [edgeShiftDirection_onsite]
  have hinter : ∀ j k : Fin n, (p + t • edgeShiftDirection i) (.interaction j k)
      = p (.interaction j k) := by
    intro j k
    simp [edgeShiftDirection_interaction]
  have hsum : (∑ j, ((p + t • edgeShiftDirection i) (.onsite j)
        + (p + t • edgeShiftDirection i) (.interaction j j)) / 2)
      = (∑ j, (p (.onsite j) + p (.interaction j j)) / 2) + -t := by
    have hterm : ∀ j : Fin n, ((p + t • edgeShiftDirection i) (.onsite j)
          + (p + t • edgeShiftDirection i) (.interaction j j)) / 2
        = (p (.onsite j) + p (.interaction j j)) / 2 + (if j = i then -t else 0) := by
      intro j
      rw [honsite j, hinter j j]
      by_cases hj : j = i
      · subst hj
        simp
        ring
      · simp [hj]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i fun _ => -t]
    simp
  have hsum2 : (∑ j, ∑ k ∈ Finset.univ.erase j,
        (p + t • edgeShiftDirection i) (.interaction j k) / 4)
      = ∑ j, ∑ k ∈ Finset.univ.erase j, p (.interaction j k) / 4 :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hinter j k]
  rw [pauliIdentityRealCoefficient, pauliIdentityRealCoefficient, hconst, hsum, hsum2]
  ring

theorem pauliIdentityCoefficient_twoLocalEdgeSlice (p : HypercubeTwoLocalParameter n → ℝ)
    (i : Fin n) (q : ℝ × ℝ) :
    pauliIdentityCoefficient (twoLocalEdgeSlice p i q)
      = ((pauliIdentityRealCoefficient p : ℝ) : ℂ) := by
  have hcongr : pauliIdentityCoefficient (twoLocalEdgeSlice p i q)
      = pauliIdentityCoefficient (fun θ => (((p + q.1 • edgeShiftDirection i) θ : ℝ) : ℂ)) := by
    rw [pauliIdentityCoefficient, pauliIdentityCoefficient, twoLocalEdgeSlice_constant]
    congr 1
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by
        rw [twoLocalEdgeSlice_onsite, twoLocalEdgeSlice_interaction]
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
        rw [twoLocalEdgeSlice_interaction]
  rw [hcongr, pauliIdentityCoefficient_ofReal, pauliIdentityRealCoefficient_edgeShift]

/-! ## The numbered traceless family -/

/-- Numbering of the nonidentity Pauli labels of weight at most `q`. -/
def pauliTracelessLabelEquivFin (n q : ℕ) :
    PauliTracelessLabel n q ≃ Fin (Fintype.card (PauliTracelessLabel n q)) :=
  Fintype.equivFin _

/-- The traceless Pauli family in numbered coefficients. -/
def pauliTracelessFinPolynomialMatrix (n q : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool)
      (MvPolynomial (Fin (Fintype.card (PauliTracelessLabel n q))) ℂ) :=
  (pauliTracelessPolynomialMatrix n q).map
    (MvPolynomial.rename (pauliTracelessLabelEquivFin n q))

theorem map_eval_pauliTracelessFinPolynomialMatrix {q : ℕ}
    (z : Fin (Fintype.card (PauliTracelessLabel n q)) → ℂ) :
    (pauliTracelessFinPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z)
      = (pauliTracelessPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          fun P => z (pauliTracelessLabelEquivFin n q P)) := by
  rw [pauliTracelessFinPolynomialMatrix, Matrix.map_map]
  have hcomp : (⇑(MvPolynomial.eval₂Hom (RingHom.id ℂ) z) ∘
        ⇑(MvPolynomial.rename (pauliTracelessLabelEquivFin n q)))
      = ⇑(MvPolynomial.eval₂Hom (RingHom.id ℂ)
        fun P => z (pauliTracelessLabelEquivFin n q P)) := by
    funext r
    show MvPolynomial.eval₂ (RingHom.id ℂ) z
        ((MvPolynomial.rename (pauliTracelessLabelEquivFin n q)) r) = _
    rw [MvPolynomial.eval₂_rename]
    rfl
  rw [hcomp]

/-- The numbered traceless Pauli coefficients of an occupation-form two-local Hamiltonian. -/
def pauliTracelessFinCoefficient {q : ℕ} (v : HypercubeTwoLocalParameter n → ℂ) :
    Fin (Fintype.card (PauliTracelessLabel n q)) → ℂ :=
  fun t => pauliTracelessCoefficient v ((pauliTracelessLabelEquivFin n q).symm t)

theorem map_eval_pauliTracelessFinCoefficient {q : ℕ} (hq : 2 ≤ q)
    (v : HypercubeTwoLocalParameter n → ℂ) :
    (pauliTracelessFinPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (pauliTracelessFinCoefficient v))
      = hypercubeTwoLocalMatrix v
        - (pauliIdentityCoefficient v) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  rw [map_eval_pauliTracelessFinPolynomialMatrix]
  have hcoeff : (fun P => pauliTracelessFinCoefficient (q := q) v
      (pauliTracelessLabelEquivFin n q P)) = pauliTracelessCoefficient v := by
    funext P
    simp [pauliTracelessFinCoefficient]
  rw [hcoeff]
  exact eval_pauliTracelessCoefficient hq v

theorem continuous_pauliTracelessFinCoefficient {q : ℕ} :
    Continuous (pauliTracelessFinCoefficient (n := n) (q := q)) := by
  refine continuous_pi fun t => ?_
  unfold pauliTracelessFinCoefficient pauliTracelessCoefficient
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · exact continuous_finsetSum _ fun i _ =>
      continuous_ite_const _ (continuous_pauliZCoefficient i)
  · refine continuous_finsetSum _ fun ij _ => ?_
    refine continuous_ite_const _ ?_
    by_cases hij : ij.1 = ij.2
    · simpa [hij] using continuous_const
    · simpa [hij] using continuous_pauliZZCoefficient ij.1 ij.2
  · exact continuous_finsetSum _ fun i _ =>
      continuous_ite_const _ (continuous_coordinate _)

/-- **Real-slice genericity of the traceless fixed-weight Pauli ensemble.**  This is the card's own
ensemble: for `q >= 2`, outside a meagre Lebesgue-null set of real coefficients of the *nonidentity*
Pauli strings of weight at most `q`, the `2^n` energies satisfy no nonzero balanced integer
relation. -/
theorem pauliTracelessFin_dense_residual_fullMeasure (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Dense (polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q)) ∧
      polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q) ∈
        residual (Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (pauliTracelessFinPolynomialMatrix n q))ᶜ = 0 :=
  polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_twoLocalEmbedding
    (pauliTracelessFinPolynomialMatrix n q) pauliTracelessFinCoefficient
    pauliIdentityRealCoefficient continuous_pauliTracelessFinCoefficient
    (fun p => by
      rw [map_eval_pauliTracelessFinCoefficient hq, pauliIdentityCoefficient_ofReal])
    (fun p i q' => by
      rw [map_eval_pauliTracelessFinCoefficient hq, pauliIdentityCoefficient_twoLocalEdgeSlice])

/-- At real coefficients a traceless Pauli combination is Hermitian. -/
theorem isHermitian_pauliTracelessFinEval {q : ℕ}
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ) :
    ((pauliTracelessFinPolynomialMatrix n q).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (p t : ℂ))).IsHermitian := by
  rw [map_eval_pauliTracelessFinPolynomialMatrix]
  refine Matrix.IsHermitian.ext fun x y => ?_
  rw [eval_pauliTracelessPolynomialMatrix, eval_pauliTracelessPolynomialMatrix, star_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [star_mul']
  have hstar : star (finitePauliMatrix P.1 y x) = finitePauliMatrix P.1 x y := by
    have h := finitePauliMatrix_isHermitian P.1
    rw [Matrix.IsHermitian] at h
    exact congrFun (congrFun h x) y
  rw [hstar]
  congr 1
  exact Complex.conj_ofReal _

/-- **The card's statement.**  For `q >= 2`, almost every real combination of nonidentity Pauli
strings of weight at most `q` has pairwise distinct energies admitting no balanced integer
relation, so its `2^n - 1` projective frequencies are rationally independent. -/
theorem pauliTraceless_simple_and_projectivelyIndependent_generically (n : ℕ) {q : ℕ}
    (hq : 2 ≤ q) :
    Dense (polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q)) ∧
      polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q) ∈
        residual (Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (pauliTracelessFinPolynomialMatrix n q))ᶜ = 0 ∧
      ∀ p ∈ polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q),
        Function.Injective (isHermitian_pauliTracelessFinEval p).eigenvalues ∧
        MaximallyProjectiveEnergy (isHermitian_pauliTracelessFinEval p).eigenvalues := by
  obtain ⟨hdense, hresidual, hvolume⟩ := pauliTracelessFin_dense_residual_fullMeasure n hq
  refine ⟨hdense, hresidual, hvolume, fun p hp => ⟨?_, ?_⟩⟩
  · exact MaximallyProjectiveEnergy.injective
      (maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ p hp _)
  · exact maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ p hp _

/-- **Almost sure spectral genericity for any full-density fixed-`q` Pauli ensemble.** -/
theorem pauliTraceless_projectivelyIndependent_ae (n : ℕ) {q : ℕ} (hq : 2 ≤ q)
    {μ : Measure (Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)} (hμ : μ ≪ volume) :
    ∀ᵐ p ∂μ, Function.Injective (isHermitian_pauliTracelessFinEval p).eigenvalues ∧
      MaximallyProjectiveEnergy (isHermitian_pauliTracelessFinEval p).eigenvalues := by
  obtain ⟨-, -, hvolume, hgeneric⟩ :=
    pauliTraceless_simple_and_projectivelyIndependent_generically n hq
  refine MeasureTheory.measure_mono_null (fun z hz => ?_) (hμ hvolume)
  by_contra hcon
  exact hz (hgeneric z (by simpa using hcon))


/-- **Rational independence of the projective frequencies of a generic Pauli Hamiltonian.**  At a
generic real coefficient vector of the nonidentity Pauli strings of weight at most `q`, the
`2^n - 1` differences `E_x - E_(x₀)` admit no nontrivial integer relation. -/
theorem pauliTraceless_projectiveFrequencies_independent (n : ℕ) {q : ℕ}
    (p : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (pauliTracelessFinPolynomialMatrix n q))
    (x₀ : Fin n → Bool) (k : (Fin n → Bool) → ℤ) (hk₀ : k x₀ = 0)
    (hk : (∑ x, (k x : ℝ) *
      ((isHermitian_pauliTracelessFinEval p).eigenvalues x
        - (isHermitian_pauliTracelessFinEval p).eigenvalues x₀)) = 0) :
    k = 0 :=
  eq_zero_of_projectiveRelation
    (maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ p hp _) x₀ k hk₀ hk

end

end GaloisForLFunctions.HTGeometry
