import GaloisForLFunctions.HTGeometry.SteinbergWeylConjugation

/-!
# Exact `A₂` upper-root normal form in the Steinberg group

For three distinct oriented roots `i → j → k`, the positive-root subgroup has a
closed coordinate system

```text
xᵢⱼ(a) xᵢₖ(b) xⱼₖ(c).
```

The multiplication correction is `−a'c`; its sign is forced by the chained
Steinberg relation.  The elementary-matrix image recovers all three
coordinates, so this lift is injective.  This is the irreducible local
collection step in Milnor's proof of the upper-unipotent normal form (Lemma
9.14); the finite-rank collector builds by iterating this `A₂` move.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*}

/-- Ordered positive-root word on a rank-three chain. -/
def steinbergUpperTriangle {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) : SteinbergGroup R n :=
  steinbergX hij a * steinbergX hik b * steinbergX hjk c

/-- The exact `A₂` collection law. -/
theorem steinbergUpperTriangle_mul {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c a' b' c' : R) :
    steinbergUpperTriangle hij hjk hik a b c * steinbergUpperTriangle hij hjk hik a' b' c'
      = steinbergUpperTriangle hij hjk hik (a + a') (b + b' - a' * c) (c + c') := by
  have hmove := steinbergX_conj_chain' hij hjk hik a' c
  have hmove' : steinbergX hjk c * steinbergX hij a'
      = steinbergX hik (- (a' * c)) * steinbergX hij a' * steinbergX hjk c := by
    rw [← mul_inv_eq_iff_eq_mul, steinbergX_neg]
    exact hmove
  have hcomm_ij_ik : steinbergX hij a' * steinbergX hik (b - a' * c)
      = steinbergX hik (b - a' * c) * steinbergX hij a' :=
    steinbergX_commute_row hij hik a' (b - a' * c)
  have hcomm_ik_jk : steinbergX hjk c * steinbergX hik b'
      = steinbergX hik b' * steinbergX hjk c :=
    (steinbergX_commute_col hik hjk b' c).symm
  rw [steinbergUpperTriangle, steinbergUpperTriangle, steinbergUpperTriangle]
  calc steinbergX hij a * steinbergX hik b * steinbergX hjk c
        * (steinbergX hij a' * steinbergX hik b' * steinbergX hjk c')
      = steinbergX hij a * steinbergX hik b
        * (steinbergX hik (- (a' * c)) * steinbergX hij a' * steinbergX hjk c)
        * steinbergX hik b' * steinbergX hjk c' := by
          calc
            _ = steinbergX hij a * steinbergX hik b
              * (steinbergX hjk c * steinbergX hij a') * steinbergX hik b' * steinbergX hjk c' := by
                group
            _ = _ := by rw [hmove']
    _ = steinbergX hij a * steinbergX hik b * steinbergX hik (- (a' * c))
        * steinbergX hij a' * steinbergX hjk c * steinbergX hik b' * steinbergX hjk c' := by
          group
    _ = steinbergX hij a * steinbergX hik (b - a' * c) * steinbergX hij a'
        * steinbergX hjk c * steinbergX hik b' * steinbergX hjk c' := by
          calc
            _ = steinbergX hij a * (steinbergX hik b * steinbergX hik (- (a' * c)))
              * steinbergX hij a' * steinbergX hjk c * steinbergX hik b' * steinbergX hjk c' := by
                group
            _ = _ := by
              rw [steinbergX_mul]
              congr 1
              ring
    _ = steinbergX hij a * steinbergX hij a' * steinbergX hik (b - a' * c)
        * steinbergX hjk c * steinbergX hik b' * steinbergX hjk c' := by
          calc
            _ = steinbergX hij a * (steinbergX hik (b - a' * c) * steinbergX hij a')
              * steinbergX hjk c * steinbergX hik b' * steinbergX hjk c' := by group
            _ = _ := by rw [hcomm_ij_ik.symm]; group
    _ = steinbergX hij (a + a') * steinbergX hik (b - a' * c)
        * steinbergX hjk c * steinbergX hik b' * steinbergX hjk c' := by rw [steinbergX_mul]
    _ = steinbergX hij (a + a') * steinbergX hik (b - a' * c)
        * steinbergX hik b' * steinbergX hjk c * steinbergX hjk c' := by
          calc
            _ = steinbergX hij (a + a') * steinbergX hik (b - a' * c)
              * (steinbergX hjk c * steinbergX hik b') * steinbergX hjk c' := by group
            _ = _ := by rw [hcomm_ik_jk]; group
    _ = steinbergX hij (a + a') * steinbergX hik (b + b' - a' * c)
        * steinbergX hjk (c + c') := by
          calc
            _ = steinbergX hij (a + a')
                * (steinbergX hik (b - a' * c) * steinbergX hik b')
                * (steinbergX hjk c * steinbergX hjk c') := by group
            _ = _ := by rw [steinbergX_mul, steinbergX_mul]; congr 1; ring

/-- Inversion in the `A₂` upper-root coordinates. -/
theorem steinbergUpperTriangle_inv {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) :
    (steinbergUpperTriangle hij hjk hik a b c)⁻¹
      = steinbergUpperTriangle hij hjk hik (-a) (-b - a * c) (-c) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [steinbergUpperTriangle_mul]
  have hleft : -a + a = (0 : R) := neg_add_cancel a
  have hmid : -b - a * c + b - a * -c = (0 : R) := by ring
  have hright : -c + c = (0 : R) := neg_add_cancel c
  rw [hleft, hmid, hright, steinbergUpperTriangle]
  rw [steinbergX_zero, steinbergX_zero, steinbergX_zero]
  simp

/-- The positive-root subgroup on a rank-three chain. -/
def steinbergUpperTriangleSubgroup {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Subgroup (SteinbergGroup R n) where
  carrier := {x | ∃ (a b c : R), x = steinbergUpperTriangle hij hjk hik a b c}
  one_mem' := ⟨0, 0, 0, by simp only [steinbergUpperTriangle, steinbergX_zero, mul_one]⟩
  mul_mem' := by
    rintro x y ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b' - a' * c, c + c', steinbergUpperTriangle_mul hij hjk hik _ _ _ _ _ _⟩
  inv_mem' := by
    rintro x ⟨a, b, c, rfl⟩
    exact ⟨-a, -b - a * c, -c, steinbergUpperTriangle_inv hij hjk hik a b c⟩

/-- The three positive-root families on a rank-three chain. -/
def steinbergUpperTriangleGens {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Set (SteinbergGroup R n) :=
  {x | (∃ a : R, x = steinbergX hij a) ∨ (∃ b : R, x = steinbergX hik b)
    ∨ ∃ c : R, x = steinbergX hjk c}

/-- The collector is precisely the subgroup generated by its three positive-root families. -/
theorem steinbergUpperTriangleSubgroup_eq_closure {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    steinbergUpperTriangleSubgroup (R := R) hij hjk hik
      = Subgroup.closure (steinbergUpperTriangleGens (R := R) hij hjk hik) := by
  apply le_antisymm
  · rintro x ⟨a, b, c, rfl⟩
    rw [steinbergUpperTriangle]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr (Or.inl ⟨b, rfl⟩))
    · exact Subgroup.subset_closure (Or.inr (Or.inr ⟨c, rfl⟩))
  · apply (Subgroup.closure_le _).2
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨a, 0, 0, by simp only [steinbergUpperTriangle, steinbergX_zero, mul_one]⟩
    · exact ⟨0, b, 0, by simp only [steinbergUpperTriangle, steinbergX_zero, one_mul, mul_one]⟩
    · exact ⟨0, 0, c, by simp only [steinbergUpperTriangle, steinbergX_zero, one_mul]⟩

section MatrixNormalForm

open Matrix

variable [DecidableEq n] [Fintype n]

/-- Matrix image of the ordered `A₂` upper-root word. -/
theorem transvection_upperTriangle {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k)
    (a b c : R) :
    Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c := by
  have hAB : (Matrix.single i j a : Matrix n n R) * Matrix.single i k b = 0 := by
    simp [Ne.symm hij]
  have hAC : (Matrix.single i j a : Matrix n n R) * Matrix.single j k c
      = Matrix.single i k (a * c) := by simp
  have hBC : (Matrix.single i k b : Matrix n n R) * Matrix.single j k c = 0 := by
    simp [Ne.symm hjk]
  calc Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      = (1 + Matrix.single i j a + Matrix.single i k b) * Matrix.transvection j k c := by
        simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
          Matrix.mul_one, hAB, add_zero]
    _ = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c := by
        simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
          Matrix.mul_one, hAC, hBC, add_zero]
        calc
          _ = 1 + Matrix.single i j a
              + (Matrix.single i k b + Matrix.single i k (a * c)) + Matrix.single j k c := by abel
          _ = _ := by rw [← Matrix.single_add]

/-- The `(i,j)` entry recovers first upper-root coordinate. -/
theorem transvection_upperTriangle_apply_ij {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c) i j = a := by
  rw [transvection_upperTriangle hij hjk hik]
  simp [hij, Ne.symm hij, Ne.symm hjk]

/-- The `(i,k)` entry recovers middle coordinate after its forced chain correction. -/
theorem transvection_upperTriangle_apply_ik {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c) i k
      = b + a * c := by
  rw [transvection_upperTriangle hij hjk hik]
  simp [hjk, hik, Ne.symm hij]

/-- The `(j,k)` entry recovers final upper-root coordinate. -/
theorem transvection_upperTriangle_apply_jk {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c) j k = c := by
  rw [transvection_upperTriangle hij hjk hik]
  simp [hij, hjk]

/-- The elementary-matrix map is injective on the rank-three positive-root subgroup. -/
theorem steinbergUpperTriangle_injective {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {a b c a' b' c' : R}
    (h : steinbergUpperTriangle hij hjk hik a b c = steinbergUpperTriangle hij hjk hik a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have himage := congrArg
    (fun x : SteinbergGroup R n => ((steinbergToGL x : (Matrix n n R)ˣ) : Matrix n n R)) h
  simp only [steinbergUpperTriangle, map_mul, steinbergToGL_x, Units.val_mul, elemUnit_val] at himage
  have ha := congrFun (congrFun himage i) j
  have hbc := congrFun (congrFun himage i) k
  have hc := congrFun (congrFun himage j) k
  rw [transvection_upperTriangle_apply_ij hij hjk hik,
    transvection_upperTriangle_apply_ij hij hjk hik] at ha
  rw [transvection_upperTriangle_apply_ik hij hjk hik,
    transvection_upperTriangle_apply_ik hij hjk hik] at hbc
  rw [transvection_upperTriangle_apply_jk hij hjk hik,
    transvection_upperTriangle_apply_jk hij hjk hik] at hc
  refine ⟨ha, ?_, hc⟩
  rw [ha, hc] at hbc
  exact add_right_cancel hbc

end MatrixNormalForm

end GaloisForLFunctions.HTGeometry

end
