import GaloisForLFunctions.HTGeometry.SiegelLovasz

/-!
# The projected norm and greedy minimality

The quantity that reduction theory minimises at level `i` is not the form itself but its projection
orthogonally to the first `i` Jacobi directions,

`projNorm i v = ∑_{m ≥ i} dₘ (Uv)ₘ²`.

At the `i`-th basis vector it is `dᵢ`, and at the next one it is `dᵢ Uᵢⱼ² + dⱼ` — exactly the
quantity the Lovász bound compares `dᵢ` against.  So greedy minimality at level `i`, which is what a
greedy basis provides, gives the Lovász bound directly.

This replaces the earlier `hpre` form of the hypothesis, which demanded that the later basis vector
have *no* component along the earlier ones.  That is too strong: a greedy lift is only ever
determined modulo the earlier vectors, so its real coordinates cannot be made to vanish — only
reduced to `[-1/2, 1/2]`.  Projecting them away is the correct move.

* `JacobiData.projNorm` : the projected squared norm.
* `JacobiData.projNorm_self`, `projNorm_succ` : its values at the two relevant basis vectors.
* `JacobiData.lovasz_of_projNorm_min` : **the Lovász bound from greedy minimality.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The squared norm of the projection of `v` orthogonally to the first `i` Jacobi directions. -/
noncomputable def JacobiData.projNorm (J : JacobiData n) (i : Fin n) (v : Fin n → ℝ) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin n => i ≤ m), J.d m * ((J.U *ᵥ v) m) ^ (2 : ℕ)

/-- The projected norm is nonnegative. -/
theorem JacobiData.projNorm_nonneg (J : JacobiData n) (i : Fin n) (v : Fin n → ℝ) :
    0 ≤ J.projNorm i v :=
  Finset.sum_nonneg fun m _ => mul_nonneg (J.pos m).le (sq_nonneg _)

/-- The projected norm is at most the value of the form. -/
theorem JacobiData.projNorm_le (J : JacobiData n) (i : Fin n) (v : Fin n → ℝ) :
    J.projNorm i v ≤ v ⬝ᵥ (J.form *ᵥ v) := by
  classical
  rw [J.quadForm_eq v]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun m _ _ => mul_nonneg (J.pos m).le (sq_nonneg _)

theorem JacobiData.mulVec_single (J : JacobiData n) (j m : Fin n) :
    (J.U *ᵥ (Pi.single j (1 : ℝ))) m = J.U m j := by
  rw [Matrix.mulVec_single]
  simp

/-- **The projected norm at the `i`-th basis vector is `dᵢ`.** -/
theorem JacobiData.projNorm_self (J : JacobiData n) (i : Fin n) :
    J.projNorm i (Pi.single i (1 : ℝ)) = J.d i := by
  classical
  rw [JacobiData.projNorm]
  refine (Finset.sum_eq_single i (fun m hm hmi => ?_) (fun hcon => ?_)).trans ?_
  · rw [Finset.mem_filter] at hm
    have hlt : i < m := lt_of_le_of_ne hm.2 (Ne.symm hmi)
    rw [J.mulVec_single, J.upper m i hlt]
    ring
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, le_refl i⟩) hcon
  · rw [J.mulVec_single, J.unit i, one_pow, mul_one]

/-- **The projected norm at the next basis vector is `dᵢ Uᵢⱼ² + dⱼ`.** -/
theorem JacobiData.projNorm_succ (J : JacobiData n) {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1) :
    J.projNorm i (Pi.single j (1 : ℝ)) = J.d i * (J.U i j) ^ (2 : ℕ) + J.d j := by
  classical
  have hij' : i < j := Fin.lt_def.2 (by omega)
  rw [JacobiData.projNorm]
  have hsplit : (∑ m ∈ Finset.univ.filter (fun m : Fin n => i ≤ m),
        J.d m * ((J.U *ᵥ (Pi.single j (1 : ℝ))) m) ^ (2 : ℕ))
      = J.d i * ((J.U *ᵥ (Pi.single j (1 : ℝ))) i) ^ (2 : ℕ)
        + ∑ m ∈ Finset.univ.filter (fun m : Fin n => i ≤ m ∧ m ≠ i),
            J.d m * ((J.U *ᵥ (Pi.single j (1 : ℝ))) m) ^ (2 : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun m : Fin n => i ≤ m)) (fun m : Fin n => m = i)]
    congr 1
    · rw [Finset.filter_filter]
      rw [Finset.filter_congr (q := fun m : Fin n => m = i) (fun m _ => by
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by rw [h], h⟩)]
      rw [Finset.filter_eq' Finset.univ i]
      simp
    · rw [Finset.filter_filter]
  rw [hsplit, J.mulVec_single]
  congr 1
  refine (Finset.sum_eq_single j (fun m hm hmj => ?_) (fun hcon => ?_)).trans ?_
  · rw [Finset.mem_filter] at hm
    have him : i ≤ m := hm.2.1
    have hne : m ≠ i := hm.2.2
    have hjm : j < m := by
      refine Fin.lt_def.2 ?_
      have h1 : (i : ℕ) ≤ (m : ℕ) := him
      have h2 : (m : ℕ) ≠ (i : ℕ) := fun hc => hne (Fin.ext hc)
      have h3 : (m : ℕ) ≠ (j : ℕ) := fun hc => hmj (Fin.ext hc)
      omega
    rw [J.mulVec_single, J.upper m j hjm]
    ring
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j,
      le_of_lt hij', fun hc => absurd (by rw [hc] : (j : ℕ) = (i : ℕ)) (by omega)⟩) hcon
  · rw [J.mulVec_single, J.unit j, one_pow, mul_one]

/-- **The Lovász bound from greedy minimality.**  If `dᵢ` does not exceed the projected norm of the
next basis vector — which is what a greedy choice of the `i`-th basis vector guarantees — then
`dᵢ ≤ (4/3) dⱼ`. -/
theorem JacobiData.lovasz_of_projNorm_min (J : JacobiData n) {i j : Fin n}
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    (hmin : J.d i ≤ J.projNorm i (Pi.single j (1 : ℝ))) : J.d i ≤ (4 / 3) * J.d j := by
  refine lovasz_of_le hred (Fin.lt_def.2 (by omega)) ?_
  rw [J.projNorm_succ hij] at hmin
  linarith [hmin]

/-- **A greedy, size reduced Jacobi datum lies in the Siegel set with parameters `(4/3, 1)`.**

Both Siegel bounds are supplied: the unipotent bound by size reduction (the diagonal contributes
`1` and the strictly lower part `0`, so `1` is the right parameter), and the diagonal bound by the
Lovász inequality at each consecutive pair.

Only the construction of a greedy basis is left: a basis whose `i`-th vector minimises the projected
norm among lattice vectors with nonzero projection. -/
theorem JacobiData.isSiegel_of_greedy (J : JacobiData n)
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    (hgreedy : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
      J.d i ≤ J.projNorm i (Pi.single j (1 : ℝ))) :
    J.IsSiegel (4 / 3) 1 := by
  refine ⟨fun i j hij => ?_, fun i j => J.entries_le_one hred i j⟩
  exact J.lovasz_of_projNorm_min hij.symm hred (hgreedy i j hij.symm)

end GaloisForLFunctions.HTGeometry
