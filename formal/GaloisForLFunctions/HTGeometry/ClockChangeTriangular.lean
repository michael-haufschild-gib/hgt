import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import GaloisForLFunctions.HTGeometry.TriangularSubstitution

/-!
# The triangular clock-change expansion

Rescaling a derivation by a unit, `δ_u = u · δ`, changes the finite jet tuple by a triangular
linear substitution whose diagonal is `1, u, u², …`:

`δ_u^n f = ∑_{j ≤ n} a_{n,j} · δ^j f`,  `a_{n,n} = u^n`,  `a_{n,j} = 0` for `j > n`,

with coefficients independent of `f`.  When the base is closed under the derivation and contains
`u`, all coefficients stay in the base, so the two jet tuples generate the same base algebra at
every order.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The rescaled derivation `δ_u = u · δ`. -/
noncomputable def clockRescale (δ : Derivation R A A) (u : A) : Derivation R A A := u • δ

@[simp] theorem clockRescale_apply (δ : Derivation R A A) (u f : A) :
    clockRescale δ u f = u * δ f := rfl

/-- **Theorem 3.1, the triangular expansion.**  Iterating a rescaled derivation is a triangular
change of the jet tuple with diagonal `u^n`. -/
theorem exists_iterate_clockRescale (δ : Derivation R A A) (K : Subalgebra R A)
    (hK : ∀ k ∈ K, δ k ∈ K) {u : A} (huK : u ∈ K) (n : ℕ) :
    ∃ a : ℕ → A, (∀ j, a j ∈ K) ∧ a n = u ^ n ∧ (∀ j, n < j → a j = 0) ∧
      (∀ f : A, ((clockRescale δ u : A → A))^[n] f
        = ∑ j ∈ Finset.range (n + 1), a j * ((δ : A → A))^[j] f) := by
  induction n with
  | zero =>
    refine ⟨fun j => if j = 0 then 1 else 0, ?_, by simp, ?_, ?_⟩
    · intro j
      by_cases hj : j = 0
      · simp [hj]
      · simp [hj]
    · intro j hj
      have hj0 : j ≠ 0 := by omega
      simp [hj0]
    · intro f
      simp
  | succ n ih =>
    obtain ⟨a, hmem, hdiag, hzero, hexp⟩ := ih
    refine ⟨fun k => u * δ (a k) + (if k = 0 then 0 else u * a (k - 1)), ?_, ?_, ?_, ?_⟩
    · intro k
      refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ huK (hK _ (hmem k))) ?_
      by_cases hk : k = 0
      · simp [hk]
      · simp only [if_neg hk]
        exact Subalgebra.mul_mem _ huK (hmem (k - 1))
    · show u * δ (a (n + 1)) + (if n + 1 = 0 then 0 else u * a (n + 1 - 1)) = u ^ (n + 1)
      have h1 : a (n + 1) = 0 := hzero (n + 1) (by omega)
      rw [h1, map_zero, mul_zero, zero_add, if_neg (by omega : ¬ (n + 1 = 0))]
      simp only [Nat.add_sub_cancel]
      rw [hdiag]
      ring
    · intro k hk
      show u * δ (a k) + (if k = 0 then 0 else u * a (k - 1)) = 0
      have h1 : a k = 0 := hzero k (by omega)
      have h2 : a (k - 1) = 0 := hzero (k - 1) (by omega)
      rw [h1, map_zero, mul_zero, zero_add, if_neg (by omega : ¬ (k = 0)), h2, mul_zero]
    · intro f
      rw [Function.iterate_succ_apply', hexp f, clockRescale_apply]
      have hderiv : δ (∑ j ∈ Finset.range (n + 1), a j * ((δ : A → A))^[j] f)
          = ∑ j ∈ Finset.range (n + 1),
            (δ (a j) * ((δ : A → A))^[j] f + a j * ((δ : A → A))^[j + 1] f) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Derivation.leibniz]
        have hnext : δ (((δ : A → A))^[j] f) = ((δ : A → A))^[j + 1] f :=
          (Function.iterate_succ_apply' (δ : A → A) j f).symm
        rw [hnext]
        simp [smul_eq_mul]
        ring
      rw [hderiv, Finset.mul_sum]
      have hsplit : ∑ j ∈ Finset.range (n + 1),
          u * (δ (a j) * ((δ : A → A))^[j] f + a j * ((δ : A → A))^[j + 1] f)
          = (∑ j ∈ Finset.range (n + 1), u * δ (a j) * ((δ : A → A))^[j] f)
            + ∑ j ∈ Finset.range (n + 1), u * a j * ((δ : A → A))^[j + 1] f := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hsplit]
      have hfirst : ∑ j ∈ Finset.range (n + 1 + 1), u * δ (a j) * ((δ : A → A))^[j] f
          = ∑ j ∈ Finset.range (n + 1), u * δ (a j) * ((δ : A → A))^[j] f := by
        rw [Finset.sum_range_succ]
        have h1 : a (n + 1) = 0 := hzero (n + 1) (by omega)
        rw [h1, map_zero, mul_zero, zero_mul, add_zero]
      have hsecond : ∑ k ∈ Finset.range (n + 1 + 1),
          (if k = 0 then 0 else u * a (k - 1)) * ((δ : A → A))^[k] f
          = ∑ j ∈ Finset.range (n + 1), u * a j * ((δ : A → A))^[j + 1] f := by
        have hshift := Finset.sum_range_succ'
          (fun k : ℕ => (if k = 0 then (0 : A) else u * a (k - 1)) * ((δ : A → A))^[k] f) (n + 1)
        rw [hshift]
        have hzeroterm : (if (0 : ℕ) = 0 then (0 : A) else u * a (0 - 1))
            * ((δ : A → A))^[0] f = 0 := by simp
        rw [hzeroterm, add_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ¬ (j + 1 = 0) := by omega
        simp only [hj, if_false, Nat.add_sub_cancel]
      calc (∑ j ∈ Finset.range (n + 1), u * δ (a j) * ((δ : A → A))^[j] f)
            + ∑ j ∈ Finset.range (n + 1), u * a j * ((δ : A → A))^[j + 1] f
          = (∑ j ∈ Finset.range (n + 1 + 1), u * δ (a j) * ((δ : A → A))^[j] f)
            + ∑ k ∈ Finset.range (n + 1 + 1),
              (if k = 0 then 0 else u * a (k - 1)) * ((δ : A → A))^[k] f := by
            rw [hfirst, hsecond]
        _ = ∑ k ∈ Finset.range (n + 1 + 1),
              (u * δ (a k) + (if k = 0 then 0 else u * a (k - 1))) * ((δ : A → A))^[k] f := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring

/-- Rescaling by a unit and by its inverse returns the original derivation. -/
theorem clockRescale_clockRescale (δ : Derivation R A A) {u w : A} (hw : u * w = 1) :
    clockRescale (clockRescale δ u) w = δ := by
  refine Derivation.ext fun f => ?_
  show w * (u * δ f) = δ f
  rw [← mul_assoc, mul_comm w u, hw, one_mul]

/-- **Theorem 3.1, the reverse expansion.**  The original jets are triangular in the rescaled
jets, with diagonal `u^{-n}`. -/
theorem exists_iterate_clockRescale_inv (δ : Derivation R A A) (K : Subalgebra R A)
    (hK : ∀ k ∈ K, δ k ∈ K) {u w : A} (hw : u * w = 1) (huK : u ∈ K)
    (hwK : w ∈ K) (n : ℕ) :
    ∃ a : ℕ → A, (∀ j, a j ∈ K) ∧ a n = w ^ n ∧ (∀ j, n < j → a j = 0) ∧
      (∀ f : A, ((δ : A → A))^[n] f
        = ∑ j ∈ Finset.range (n + 1), a j * ((clockRescale δ u : A → A))^[j] f) := by
  have hstable : ∀ k ∈ K, (clockRescale δ u) k ∈ K := by
    intro k hk
    exact Subalgebra.mul_mem _ huK (hK k hk)
  obtain ⟨a, hmem, hdiag, hzero, hexp⟩ :=
    exists_iterate_clockRescale (clockRescale δ u) K hstable hwK n
  refine ⟨a, hmem, hdiag, hzero, fun f => ?_⟩
  have hEq : clockRescale (clockRescale δ u) w = δ := clockRescale_clockRescale δ hw
  have hval := hexp f
  rw [hEq] at hval
  exact hval

/-- **Theorem 3.1(3.2).**  The rescaled and original jet tuples generate the same base algebra at
every order: the clock change is a base-triangular change of jet coordinates. -/
theorem adjoin_jets_clockRescale (δ : Derivation R A A) (K : Subalgebra R A)
    (hK : ∀ k ∈ K, δ k ∈ K) {u w : A} (hw : u * w = 1) (huK : u ∈ K)
    (hwK : w ∈ K) (f : A) (n : ℕ) :
    Algebra.adjoin R ((K : Set A) ∪ (fun j => ((clockRescale δ u : A → A))^[j] f) '' Set.Iic n)
      = Algebra.adjoin R ((K : Set A) ∪ (fun j => ((δ : A → A))^[j] f) '' Set.Iic n) := by
  have hgen : ∀ (F G : ℕ → A),
      (∀ m ≤ n, ∃ a : ℕ → A, (∀ j, a j ∈ K) ∧
        F m = ∑ j ∈ Finset.range (m + 1), a j * G j) →
      Algebra.adjoin R ((K : Set A) ∪ (fun j => F j) '' Set.Iic n)
        ≤ Algebra.adjoin R ((K : Set A) ∪ (fun j => G j) '' Set.Iic n) := by
    intro F G hrel
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨m, hm, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl hx)
    · obtain ⟨a, hamem, haval⟩ := hrel m hm
      show F m ∈ Algebra.adjoin R ((K : Set A) ∪ (fun j => G j) '' Set.Iic n)
      rw [haval]
      refine Subalgebra.sum_mem _ fun j hj => ?_
      refine Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl (hamem j))) ?_
      refine Algebra.subset_adjoin (Or.inr ⟨j, ?_, rfl⟩)
      have hjm : j < m + 1 := Finset.mem_range.mp hj
      have hmn : m ≤ n := hm
      show j ≤ n
      omega
  refine le_antisymm (hgen _ _ fun m _ => ?_) (hgen _ _ fun m _ => ?_)
  · obtain ⟨a, hamem, -, -, haval⟩ := exists_iterate_clockRescale δ K hK huK m
    exact ⟨a, hamem, haval f⟩
  · obtain ⟨a, hamem, -, -, haval⟩ :=
      exists_iterate_clockRescale_inv δ K hK hw huK hwK m
    exact ⟨a, hamem, haval f⟩

/-! ## Clock covariance of hypertranscendence -/

/-- Differential algebraicity of `f` over a base subalgebra for a selected derivation. -/
def IsDifferentiallyAlgebraicOver (K : Subalgebra R A) (δ : Derivation R A A) (f : A) : Prop :=
  ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) K), P ≠ 0 ∧
    MvPolynomial.aeval (fun j : Fin (n + 1) => ((δ : A → A)^[(j : ℕ)] f)) P = 0

/-- Hypertranscendence of `f` over a base subalgebra for a selected derivation. -/
def IsHypertranscendentalOver (K : Subalgebra R A) (δ : Derivation R A A) (f : A) : Prop :=
  ¬ IsDifferentiallyAlgebraicOver K δ f

/-- One direction of the clock covariance: a triangular jet substitution carries a nonzero
differential relation to a nonzero differential relation. -/
theorem isDifferentiallyAlgebraicOver_of_triangular
    (K : Subalgebra R A) {δ δ' : Derivation R A A} {v v' : A} (hvK : v ∈ K)
    (hv : v * v' = 1) (hvinv : v' ∈ K)
    (hexp : ∀ n : ℕ, ∃ a : ℕ → A, (∀ j, a j ∈ K) ∧ a n = v ^ n ∧ (∀ j, n < j → a j = 0) ∧
      (∀ f : A, ((δ' : A → A))^[n] f = ∑ j ∈ Finset.range (n + 1), a j * ((δ : A → A))^[j] f))
    (f : A) (hDA : IsDifferentiallyAlgebraicOver K δ' f) :
    IsDifferentiallyAlgebraicOver K δ f := by
  classical
  obtain ⟨n, P, hP0, hPval⟩ := hDA
  choose a hamem hadiag hazero haval using hexp
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    fun j i => ⟨a (j : ℕ) (i : ℕ), hamem (j : ℕ) (i : ℕ)⟩ with hM
  have hmul' : v' * v = 1 := by rw [mul_comm]; exact hv
  have hvunit : IsUnit (⟨v, hvK⟩ : K) := by
    refine ⟨⟨⟨v, hvK⟩, ⟨v', hvinv⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext hv
    · exact Subtype.ext hmul'
  have htri : ∀ i j : Fin (n + 1), j < i → M j i = 0 := by
    intro i j hji
    apply Subtype.ext
    show a (j : ℕ) (i : ℕ) = 0
    exact hazero (j : ℕ) (i : ℕ) (by exact_mod_cast hji)
  have hdiag : ∀ i : Fin (n + 1), IsUnit (M i i) := by
    intro i
    have : M i i = (⟨v, hvK⟩ : K) ^ (i : ℕ) := by
      apply Subtype.ext
      show a (i : ℕ) (i : ℕ) = _
      rw [hadiag (i : ℕ)]
      rfl
    rw [this]
    exact hvunit.pow _
  have hdet : IsUnit M.det := isUnit_det_of_lowerTriangular htri hdiag
  refine ⟨n, linSub M P, fun hzero => hP0 (linSub_injective hdet (by rw [hzero, map_zero])), ?_⟩
  have hcomp : (MvPolynomial.aeval
      (fun j : Fin (n + 1) => ((δ : A → A)^[(j : ℕ)] f))).comp (linSub M)
      = MvPolynomial.aeval (fun j : Fin (n + 1) => ((δ' : A → A)^[(j : ℕ)] f)) := by
    rw [linSub, MvPolynomial.comp_aeval]
    congr 1
    funext j
    rw [map_sum]
    have hterm : ∀ i : Fin (n + 1),
        (MvPolynomial.aeval (fun k : Fin (n + 1) => ((δ : A → A)^[(k : ℕ)] f)))
          (MvPolynomial.C (M j i) * MvPolynomial.X i)
          = a (j : ℕ) (i : ℕ) * ((δ : A → A)^[(i : ℕ)] f) := by
      intro i
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [haval (j : ℕ) f]
    rw [Fin.sum_univ_eq_sum_range (fun i => a (j : ℕ) i * ((δ : A → A)^[i] f)) (n + 1)]
    have hjlt : (j : ℕ) < n + 1 := j.isLt
    have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range (n + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    refine (Finset.sum_subset hsub ?_).symm
    · intro i _ hi
      have hi' : ¬ (i < (j : ℕ) + 1) := by
        intro hlt
        exact hi (Finset.mem_range.mpr hlt)
      rw [hazero (j : ℕ) i (by omega), zero_mul]
  have := congrArg (fun φ : MvPolynomial (Fin (n + 1)) K →ₐ[K] A => φ P) hcomp
  simp only [AlgHom.comp_apply] at this
  rw [this, hPval]


/-- **Theorem 3.1.**  Differential algebraicity over a base closed under the derivation and
containing the clock unit is invariant under the base-defined clock torsor; equivalently
hypertranscendence is a clock-line invariant. -/
theorem isDifferentiallyAlgebraicOver_clockRescale_iff
    (δ : Derivation R A A) (K : Subalgebra R A) (hK : ∀ k ∈ K, δ k ∈ K)
    {u w : A} (hw : u * w = 1) (huK : u ∈ K) (hwK : w ∈ K) (f : A) :
    IsDifferentiallyAlgebraicOver K (clockRescale δ u) f
      ↔ IsDifferentiallyAlgebraicOver K δ f := by
  constructor
  · exact isDifferentiallyAlgebraicOver_of_triangular K huK hw hwK
      (fun n => exists_iterate_clockRescale δ K hK huK n) f
  · refine isDifferentiallyAlgebraicOver_of_triangular K hwK (by rw [mul_comm]; exact hw) huK
      (fun n => exists_iterate_clockRescale_inv δ K hK hw huK hwK n) f

/-- **Theorem 3.1.**  Hypertranscendence is invariant under the base clock torsor. -/
theorem isHypertranscendentalOver_clockRescale_iff
    (δ : Derivation R A A) (K : Subalgebra R A) (hK : ∀ k ∈ K, δ k ∈ K)
    {u w : A} (hw : u * w = 1) (huK : u ∈ K) (hwK : w ∈ K) (f : A) :
    IsHypertranscendentalOver K (clockRescale δ u) f
      ↔ IsHypertranscendentalOver K δ f := by
  rw [IsHypertranscendentalOver, IsHypertranscendentalOver,
    isDifferentiallyAlgebraicOver_clockRescale_iff δ K hK hw huK hwK f]

end GaloisForLFunctions.HTGeometry
