import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelBoundaryKernel

namespace RHTower
noncomputable section

open MvPolynomial

/-- Source ring whose variables are finite low coordinates and all special minors. -/
abbrev DeningerHazewinkelClearingSource (r : ℕ) :=
  MvPolynomial (Fin (2 * (r + 1) + 1) ⊕ ℕ) ℤ

/-- Universal low/special-minor parametrization used for denominator clearing. -/
def deningerHazewinkelClearingHom (r : ℕ) :
    DeningerHazewinkelClearingSource r →+* MvPolynomial ℕ ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C <| Sum.elim
    (fun i => MvPolynomial.X i.val)
    (fun t => deningerHazewinkelSpecialMinor (r + 2) (r + 2 + t))

/-- Source representative of the leading determinant. -/
def deningerHazewinkelClearingLeading (r : ℕ) :
    DeningerHazewinkelClearingSource r :=
  MvPolynomial.rename Sum.inl (deningerHazewinkelLowLeading (r + 1))

theorem deningerHazewinkelClearingHom_leading (r : ℕ) :
    deningerHazewinkelClearingHom r
      (deningerHazewinkelClearingLeading r) =
      deningerHazewinkelLeadingDeterminant (r + 2) := by
  rw [deningerHazewinkelClearingLeading, deningerHazewinkelClearingHom,
    MvPolynomial.eval₂Hom_rename]
  rw [← deningerHazewinkelLowLeading_rename]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro z
    simp
  · intro i
    simp [deningerHazewinkelLowEmbedding]

/-- Subring of elements whose denominator can be cleared into a fixed subring by a power of `D`. -/
def deningerPowerClosure {R : Type*} [CommRing R]
    (D : R) (A : Subring R) (hD : D ∈ A) : Subring R where
  carrier := {p | ∃ e : ℕ, D ^ e * p ∈ A}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro p q ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨e + f, ?_⟩
    rw [pow_add]
    have hDf : D ^ f ∈ A := A.pow_mem hD f
    have hDe : D ^ e ∈ A := A.pow_mem hD e
    convert A.add_mem (A.mul_mem hDf he) (A.mul_mem hDe hf) using 1 <;> ring
  neg_mem' := by
    rintro p ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [mul_neg]
    exact A.neg_mem he
  mul_mem' := by
    rintro p q ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨e + f, ?_⟩
    rw [pow_add]
    convert A.mul_mem he hf using 1 <;> ring

theorem deningerPowerClosure_iff {R : Type*} [CommRing R]
    (D : R) (A : Subring R) (hD : D ∈ A) (p : R) :
    p ∈ deningerPowerClosure D A hD ↔
      ∃ e : ℕ, D ^ e * p ∈ A := Iff.rfl

theorem mvPolynomial_mem_subring_of_vars
    {σ : Type*} (A : Subring (MvPolynomial σ ℤ))
    {p : MvPolynomial σ ℤ}
    (hX : ∀ i, i ∈ p.vars → MvPolynomial.X i ∈ A) : p ∈ A := by
  classical
  rw [p.as_sum]
  apply A.sum_mem
  intro d hd
  rw [MvPolynomial.monomial_eq]
  apply A.mul_mem
  · simpa using intCast_mem A (MvPolynomial.coeff d p)
  · apply A.prod_mem
    intro i hi
    apply A.pow_mem
    apply hX i
    exact (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩

/-- Every ambient polynomial can be moved into the low/special-minor image by multiplying by
some leading-determinant power. -/
theorem deningerHazewinkel_exists_power_mul_mem_clearingRange
    (r : ℕ) (p : MvPolynomial ℕ ℤ) :
    ∃ e : ℕ, deningerHazewinkelLeadingDeterminant (r + 2) ^ e * p ∈
      RingHom.range (deningerHazewinkelClearingHom r) := by
  let D := deningerHazewinkelLeadingDeterminant (r + 2)
  let A := RingHom.range (deningerHazewinkelClearingHom r)
  have hD : D ∈ A := ⟨deningerHazewinkelClearingLeading r,
    deningerHazewinkelClearingHom_leading r⟩
  let C := deningerPowerClosure D A hD
  have hX : ∀ i : ℕ, MvPolynomial.X i ∈ C := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        by_cases hi : i < 2 * (r + 1) + 1
        · refine ⟨0, ?_⟩
          simp only [pow_zero, one_mul]
          exact ⟨MvPolynomial.X (Sum.inl ⟨i, hi⟩), by
            simp [deningerHazewinkelClearingHom]⟩
        · have hcut : 2 * (r + 1) + 1 ≤ i := Nat.le_of_not_gt hi
          obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hcut
          let s := r + 2 + t
          have hpivot := deningerHazewinkelSpecialMinor_pivot_laplace
            (n := r + 2) (s := s)
          have hindex : r + 2 + s - 1 = 2 * (r + 1) + 1 + t := by
            dsimp only [s]
            omega
          rw [deningerHazewinkelUniversalCoeff_pivot (by omega : 1 ≤ r + 2),
            hindex] at hpivot
          have hminor : deningerHazewinkelSpecialMinor (r + 2) s ∈ C := by
            refine ⟨0, ?_⟩
            simp only [pow_zero, one_mul]
            exact ⟨MvPolynomial.X (Sum.inr t), by
              simp [deningerHazewinkelClearingHom, s]⟩
          have hrem : deningerHazewinkelSpecialLaplaceRemainder (r + 2) s ∈ C := by
            apply mvPolynomial_mem_subring_of_vars C
            intro j hj
            apply ih j
            have hjlt := deningerHazewinkelSpecialLaplaceRemainder_vars_lt
              (n := r + 2) (s := s) (by omega) (by omega) hj
            exact (by dsimp only [s] at hjlt; omega)
          have hDX : D * MvPolynomial.X (2 * (r + 1) + 1 + t) ∈ C := by
            change deningerHazewinkelLeadingDeterminant (r + 2) *
              MvPolynomial.X (2 * (r + 1) + 1 + t) ∈ C
            rw [show deningerHazewinkelLeadingDeterminant (r + 2) *
                MvPolynomial.X (2 * (r + 1) + 1 + t) =
              deningerHazewinkelSpecialMinor (r + 2) s -
                deningerHazewinkelSpecialLaplaceRemainder (r + 2) s by
                  rw [hpivot]
                  ring]
            exact C.sub_mem hminor hrem
          rcases hDX with ⟨e, he⟩
          refine ⟨e + 1, ?_⟩
          convert he using 1 <;> simp [D, pow_succ'] <;> ring
  have hpC : p ∈ C := mvPolynomial_mem_subring_of_vars C
    (fun i _ => hX i)
  exact hpC

/-- Source ideal generated by all special-minor coordinates. -/
def deningerHazewinkelClearingTailIdeal (r : ℕ) :
    Ideal (DeningerHazewinkelClearingSource r) :=
  Ideal.span (Set.range fun t : ℕ => MvPolynomial.X (Sum.inr t))

theorem deningerHazewinkelSpecialMinor_eq_zero_of_lt
    {n s : ℕ} (hs : s < n) :
    deningerHazewinkelSpecialMinor n s = 0 := by
  let j : Fin (n + 1) := ⟨s, by omega⟩
  rw [deningerHazewinkelSpecialMinor]
  apply Matrix.det_zero_of_column_eq (i := j) (j := Fin.last n)
  · intro h
    have := congrArg Fin.val h
    simp [j] at this
    omega
  · intro i
    simp [deningerHazewinkelSpecialMatrix, j]

theorem deningerHazewinkelClearingTailIdeal_map (r : ℕ) :
    Ideal.map (deningerHazewinkelClearingHom r)
      (deningerHazewinkelClearingTailIdeal r) =
      deningerHazewinkelSpecialMinorIdeal (r + 2) := by
  apply le_antisymm
  · rw [deningerHazewinkelClearingTailIdeal, Ideal.map_span,
      Ideal.span_le]
    rintro z ⟨x, ⟨t, rfl⟩, rfl⟩
    simpa [deningerHazewinkelClearingHom] using
      deningerHazewinkelSpecialMinor_mem_specialIdeal (r + 2) (r + 2 + t)
  · rw [deningerHazewinkelSpecialMinorIdeal, Ideal.span_le]
    rintro z ⟨s, rfl⟩
    rw [← deningerHazewinkelSpecialMinor_eq_updateCol]
    by_cases hs : s < r + 2
    · rw [deningerHazewinkelSpecialMinor_eq_zero_of_lt hs]
      exact (Ideal.map _ _).zero_mem
    · have hle : r + 2 ≤ s := Nat.le_of_not_gt hs
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [show deningerHazewinkelSpecialMinor (r + 2) (r + 2 + t) =
        deningerHazewinkelClearingHom r (MvPolynomial.X (Sum.inr t)) by
          simp [deningerHazewinkelClearingHom]]
      apply Ideal.mem_map_of_mem (deningerHazewinkelClearingHom r)
      apply Ideal.subset_span
      exact ⟨t, rfl⟩

/-- Finite clearing certificate for every element of the special ideal. -/
theorem deningerHazewinkel_exists_power_mul_eq_clearing_of_mem_specialIdeal
    (r : ℕ) {p : MvPolynomial ℕ ℤ}
    (hp : p ∈ deningerHazewinkelSpecialMinorIdeal (r + 2)) :
    ∃ (e : ℕ) (q : DeningerHazewinkelClearingSource r),
      q ∈ deningerHazewinkelClearingTailIdeal r ∧
      deningerHazewinkelClearingHom r q =
        deningerHazewinkelLeadingDeterminant (r + 2) ^ e * p := by
  rw [deningerHazewinkelSpecialMinorIdeal] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      rw [← deningerHazewinkelSpecialMinor_eq_updateCol]
      by_cases hs : s < r + 2
      · rw [deningerHazewinkelSpecialMinor_eq_zero_of_lt hs]
        exact ⟨0, 0, (deningerHazewinkelClearingTailIdeal r).zero_mem, by simp⟩
      · have hle : r + 2 ≤ s := Nat.le_of_not_gt hs
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
        refine ⟨0, MvPolynomial.X (Sum.inr t), ?_, ?_⟩
        · apply Ideal.subset_span
          exact ⟨t, rfl⟩
        · simp [deningerHazewinkelClearingHom]
  | zero =>
      exact ⟨0, 0, (deningerHazewinkelClearingTailIdeal r).zero_mem, by simp⟩
  | add x y hx hy hxcert hycert =>
      obtain ⟨e, q, hqI, hq⟩ := hxcert
      obtain ⟨f, u, huI, hu⟩ := hycert
      refine ⟨e + f,
        deningerHazewinkelClearingLeading r ^ f * q +
          deningerHazewinkelClearingLeading r ^ e * u, ?_, ?_⟩
      · apply (deningerHazewinkelClearingTailIdeal r).add_mem
        · exact (deningerHazewinkelClearingTailIdeal r).mul_mem_left _ hqI
        · exact (deningerHazewinkelClearingTailIdeal r).mul_mem_left _ huI
      · simp only [map_add, map_mul, map_pow,
          deningerHazewinkelClearingHom_leading, hq, hu, pow_add]
        ring
  | smul c x hx hxcert =>
      obtain ⟨f, q, hqI, hq⟩ := hxcert
      obtain ⟨e, hc⟩ :=
        deningerHazewinkel_exists_power_mul_mem_clearingRange r c
      obtain ⟨a, ha⟩ := hc
      refine ⟨e + f, a * q, ?_, ?_⟩
      · exact (deningerHazewinkelClearingTailIdeal r).mul_mem_left a hqI
      · rw [map_mul, ha, hq, pow_add]
        simp only [smul_eq_mul]
        ring

end
end RHTower

