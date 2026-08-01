import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# The Hilbert--Schmidt norm dominates every pointwise value on the unit sphere

A unit vector extends to a Hilbert basis, and the Hilbert--Schmidt norm squared is the sum over any
Hilbert basis of the squared image norms.  One term of a convergent nonnegative sum is at most the
sum, so the image of a unit vector never exceeds the Hilbert--Schmidt norm.

This is the bridge from a quantitative lower bound on the action of an operator on an explicit unit
vector to a lower bound on its Hilbert--Schmidt energy.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Pointwise domination.**  On a unit vector the image norm squared is at most the squared
Hilbert--Schmidt norm. -/
theorem norm_sq_apply_le_hsNormSq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {x : E} (hx : ‖x‖ = 1) : ‖T x‖ ^ 2 ≤ hsNormSq T := by
  have hortho : Orthonormal 𝕜 ((↑) : ({x} : Set E) → E) := by
    constructor
    · rintro ⟨v, hv⟩
      rw [Set.mem_singleton_iff] at hv
      simpa [hv] using hx
    · rintro ⟨v, hv⟩ ⟨u, hu⟩ hne
      rw [Set.mem_singleton_iff] at hv hu
      exact absurd (Subtype.ext (hv.trans hu.symm)) hne
  obtain ⟨w, b, hsub, hb⟩ := hortho.exists_hilbertBasis_extension
  have hxw : x ∈ w := hsub (Set.mem_singleton x)
  have hbx : b ⟨x, hxw⟩ = x := by rw [hb]
  have hsummable : Summable fun i : w => ‖T (b i)‖ ^ 2 :=
    summable_normSq_basis_of_basis (hsBasis 𝕜 E) b T hT
  have hsum : hsNormSq T = ∑' i : w, ‖T (b i)‖ ^ 2 := hsNormSq_eq hT b
  rw [hsum, ← hbx]
  exact Summable.le_tsum hsummable ⟨x, hxw⟩ fun j _ => by positivity

/-- **Family domination.**  On a finite orthonormal family the total image energy is at most the
squared Hilbert--Schmidt norm: the family extends to a Hilbert basis, and a finite subsum of a
nonnegative convergent sum is at most the sum. -/
theorem sum_norm_sq_apply_le_hsNormSq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} [Fintype ι] {e : ι → E} (he : Orthonormal 𝕜 e) :
    ∑ i, ‖T (e i)‖ ^ 2 ≤ hsNormSq T := by
  classical
  have hinj : Function.Injective e := he.linearIndependent.injective
  have hortho : Orthonormal 𝕜 ((↑) : Set.range e → E) :=
    (orthonormal_subtype_range hinj).mpr he
  obtain ⟨w, b, hsub, hb⟩ := hortho.exists_hilbertBasis_extension
  have hmem : ∀ i : ι, e i ∈ w := fun i => hsub (Set.mem_range_self i)
  set f : ι → w := fun i => ⟨e i, hmem i⟩ with hf
  have hfinj : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hbf : ∀ i : ι, b (f i) = e i := fun i => by rw [hb]
  have hsummable : Summable fun i : w => ‖T (b i)‖ ^ 2 :=
    summable_normSq_basis_of_basis (hsBasis 𝕜 E) b T hT
  have hsum : hsNormSq T = ∑' i : w, ‖T (b i)‖ ^ 2 := hsNormSq_eq hT b
  have hrewrite : ∑ i, ‖T (e i)‖ ^ 2 = ∑ x ∈ Finset.univ.image f, ‖T (b x)‖ ^ 2 := by
    rw [Finset.sum_image fun i _ j _ hij => hfinj hij]
    exact Finset.sum_congr rfl fun i _ => by rw [hbf i]
  rw [hsum, hrewrite]
  exact Summable.sum_le_tsum _ (fun i _ => by positivity) hsummable

/-- An operator that is isometric on a finite orthonormal family has at least the family's
cardinality as Hilbert--Schmidt energy. -/
theorem card_le_hsNormSq_of_norm_apply_eq_one {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} [Fintype ι] {e : ι → E} (he : Orthonormal 𝕜 e)
    (hnorm : ∀ i, 1 ≤ ‖T (e i)‖) :
    (Fintype.card ι : ℝ) ≤ hsNormSq T := by
  refine le_trans ?_ (sum_norm_sq_apply_le_hsNormSq hT he)
  have hterm : ∀ i : ι, (1 : ℝ) ≤ ‖T (e i)‖ ^ 2 := by
    intro i
    have h := hnorm i
    nlinarith [norm_nonneg (T (e i))]
  calc (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ ∑ i, ‖T (e i)‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i

end RHTower
