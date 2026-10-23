import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Monomials in a coordinate are total in `L²`

On a compact space with a finite regular measure, an injective continuous coordinate generates a
subalgebra of continuous functions that separates points, so Stone--Weierstrass makes polynomials in
that coordinate uniformly dense.  Continuous functions being dense in `L²`, the monomials in the
coordinate are a total family: only the zero vector is orthogonal to all of them.

This is what makes the *first visible degree* of a bounded observable well defined — the observable
cannot annihilate every monomial without vanishing on the whole space.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Coordinates

variable {Ω : Type*} [TopologicalSpace Ω]

/-- The complex monomial in a continuous coordinate, as a continuous function. -/
def coordMonomialCM (X : C(Ω, ℝ)) (n : ℕ) : C(Ω, ℂ) :=
  ⟨fun ω => ((X ω : ℝ) : ℂ) ^ n, by fun_prop⟩

@[simp]
theorem coordMonomialCM_apply (X : C(Ω, ℝ)) (n : ℕ) (ω : Ω) :
    coordMonomialCM X n ω = ((X ω : ℝ) : ℂ) ^ n := rfl

/-- The complexification of a real continuous function. -/
def toComplexCM (f : C(Ω, ℝ)) : C(Ω, ℂ) := ⟨fun ω => ((f ω : ℝ) : ℂ), by fun_prop⟩

@[simp]
theorem toComplexCM_apply (f : C(Ω, ℝ)) (ω : Ω) : toComplexCM f ω = ((f ω : ℝ) : ℂ) := rfl

theorem toComplexCM_pow (X : C(Ω, ℝ)) (n : ℕ) :
    toComplexCM (X ^ n) = coordMonomialCM X n := by
  ext ω
  simp [toComplexCM, coordMonomialCM]

theorem toComplexCM_smul (r : ℝ) (f : C(Ω, ℝ)) :
    toComplexCM (r • f) = ((r : ℂ)) • toComplexCM f := by
  ext ω
  simp [toComplexCM]

theorem toComplexCM_add (f g : C(Ω, ℝ)) :
    toComplexCM (f + g) = toComplexCM f + toComplexCM g := by
  ext ω
  simp [toComplexCM]

theorem toComplexCM_zero : toComplexCM (0 : C(Ω, ℝ)) = 0 := by
  ext ω
  simp [toComplexCM]

end Coordinates

section Pairing

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [MeasurableSpace Ω] [BorelSpace Ω] in
theorem norm_toComplexCM (f : C(Ω, ℝ)) : ‖toComplexCM f‖ = ‖f‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
  congr 1
  funext ω
  rw [toComplexCM_apply, Complex.norm_real]

/-- The evaluation functional against a fixed `L²` vector, on real continuous functions. -/
def realPairing (g : Lp ℂ 2 μ) : C(Ω, ℝ) → ℂ :=
  fun f => inner ℂ g (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (toComplexCM f))

theorem realPairing_add (g : Lp ℂ 2 μ) (f₁ f₂ : C(Ω, ℝ)) :
    realPairing g (f₁ + f₂) = realPairing g f₁ + realPairing g f₂ := by
  rw [realPairing, realPairing, realPairing, toComplexCM_add, map_add, inner_add_right]

theorem realPairing_smul (g : Lp ℂ 2 μ) (r : ℝ) (f : C(Ω, ℝ)) :
    realPairing g (r • f) = (r : ℂ) * realPairing g f := by
  rw [realPairing, realPairing, toComplexCM_smul, map_smul, inner_smul_right]

theorem realPairing_zero (g : Lp ℂ 2 μ) : realPairing g 0 = 0 := by
  rw [realPairing, toComplexCM_zero, map_zero, inner_zero_right]

theorem norm_realPairing_le (g : Lp ℂ 2 μ) (f : C(Ω, ℝ)) :
    ‖realPairing g f‖ ≤ ‖g‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ : C(Ω, ℂ) →L[ℂ] Lp ℂ 2 μ)‖
      * ‖f‖) := by
  refine le_trans (norm_inner_le_norm _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _) ?_
  rw [norm_toComplexCM]

theorem continuous_realPairing (g : Lp ℂ 2 μ) : Continuous (realPairing g) := by
  have hlin : ∀ f₁ f₂ : C(Ω, ℝ),
      realPairing g f₁ - realPairing g f₂ = realPairing g (f₁ - f₂) := by
    intro f₁ f₂
    have h := realPairing_add g (f₁ - f₂) f₂
    rw [sub_add_cancel] at h
    rw [h]
    ring
  refine Metric.continuous_iff.mpr fun f ε hε => ?_
  set C : ℝ := ‖g‖ * ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ : C(Ω, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨ε / (C + 1), by positivity, fun f' hf' => ?_⟩
  rw [dist_eq_norm, hlin f' f]
  have hb := norm_realPairing_le g (f' - f)
  have hdist : ‖f' - f‖ < ε / (C + 1) := by
    rwa [← dist_eq_norm]
  calc ‖realPairing g (f' - f)‖ ≤ C * ‖f' - f‖ := by
        refine hb.trans (le_of_eq ?_)
        rw [hC]
        ring
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hdist.le hC0
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hε.le]

theorem realPairing_sum (g : Lp ℂ 2 μ) {ι : Type*} (s : Finset ι) (f : ι → C(Ω, ℝ)) :
    realPairing g (∑ i ∈ s, f i) = ∑ i ∈ s, realPairing g (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [realPairing_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, realPairing_add, ih]

/-- **Stone--Weierstrass along the coordinate.**  If the pairing kills every power of an injective
continuous coordinate, it kills every continuous real function. -/
theorem realPairing_eq_zero_of_powers {X : C(Ω, ℝ)} (hX : Function.Injective X)
    (g : Lp ℂ 2 μ) (hg : ∀ n : ℕ, realPairing g (X ^ n) = 0) (f : C(Ω, ℝ)) :
    realPairing g f = 0 := by
  have hclosed : IsClosed {h : C(Ω, ℝ) | realPairing g h = 0} :=
    isClosed_eq (continuous_realPairing g) continuous_const
  have hpoly : ∀ p : Polynomial ℝ, realPairing g (Polynomial.aeval X p) = 0 := by
    intro p
    rw [Polynomial.aeval_eq_sum_range, realPairing_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [realPairing_smul, hg i, mul_zero]
  have hsep : (Algebra.adjoin ℝ {X}).SeparatesPoints := by
    intro x y hxy
    exact ⟨X, ⟨X, Algebra.self_mem_adjoin_singleton ℝ X, rfl⟩, fun h => hxy (hX h)⟩
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (Algebra.adjoin ℝ {X}) hsep
  have hmem : f ∈ closure ((Algebra.adjoin ℝ {X} : Subalgebra ℝ C(Ω, ℝ)) : Set C(Ω, ℝ)) := by
    have hf : f ∈ (Algebra.adjoin ℝ {X}).topologicalClosure := by
      rw [htop]
      trivial
    exact hf
  have hsub : ((Algebra.adjoin ℝ {X} : Subalgebra ℝ C(Ω, ℝ)) : Set C(Ω, ℝ))
      ⊆ {h : C(Ω, ℝ) | realPairing g h = 0} := by
    intro h hh
    rw [SetLike.mem_coe, Algebra.adjoin_singleton_eq_range_aeval] at hh
    obtain ⟨p, rfl⟩ := hh
    exact hpoly p
  exact hclosed.closure_subset_iff.mpr hsub hmem

/-- The real part of a continuous complex function. -/
def reCM (f : C(Ω, ℂ)) : C(Ω, ℝ) := ⟨fun ω => (f ω).re, by fun_prop⟩

/-- The imaginary part of a continuous complex function. -/
def imCM (f : C(Ω, ℂ)) : C(Ω, ℝ) := ⟨fun ω => (f ω).im, by fun_prop⟩

omit [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
theorem toComplexCM_re_add_im (f : C(Ω, ℂ)) :
    toComplexCM (reCM f) + Complex.I • toComplexCM (imCM f) = f := by
  ext ω
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, toComplexCM_apply, reCM, imCM,
    ContinuousMap.coe_mk, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im (f ω)

variable [T2Space Ω] [μ.WeaklyRegular]

/-- **Monomials in an injective continuous coordinate are total in `L²`.**  Only the zero vector is
orthogonal to every one of them. -/
theorem eq_zero_of_inner_coordMonomial_eq_zero {X : C(Ω, ℝ)} (hX : Function.Injective X)
    (g : Lp ℂ 2 μ)
    (hg : ∀ n : ℕ,
      (inner ℂ g (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n)) : ℂ) = 0) :
    g = 0 := by
  have hpow : ∀ n : ℕ, realPairing g (X ^ n) = 0 := by
    intro n
    rw [realPairing, toComplexCM_pow]
    exact hg n
  have hreal := realPairing_eq_zero_of_powers hX g hpow
  have hcomplex : ∀ f : C(Ω, ℂ),
      (inner ℂ g (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f) : ℂ) = 0 := by
    intro f
    rw [← toComplexCM_re_add_im f, map_add, map_smul, inner_add_right, inner_smul_right]
    rw [show (inner ℂ g (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (toComplexCM (reCM f))) : ℂ)
        = realPairing g (reCM f) from rfl,
      show (inner ℂ g (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (toComplexCM (imCM f))) : ℂ)
        = realPairing g (imCM f) from rfl, hreal (reCM f), hreal (imCM f)]
    ring
  have hclosed : IsClosed {v : Lp ℂ 2 μ | (inner ℂ g v : ℂ) = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hdense := ContinuousMap.toLp_denseRange (p := 2) ℂ μ ℂ (by norm_num)
  have hall : ∀ v : Lp ℂ 2 μ, (inner ℂ g v : ℂ) = 0 := by
    intro v
    refine hclosed.closure_subset_iff.mpr ?_ (hdense v)
    rintro _ ⟨f, rfl⟩
    exact hcomplex f
  have := hall g
  exact inner_self_eq_zero.mp this

/-- **The monomials in an injective continuous coordinate span a dense subspace of `L²`.** -/
theorem dense_span_coordMonomial {X : C(Ω, ℝ)} (hX : Function.Injective X) :
    Dense ((Submodule.span ℂ (Set.range
      (fun n : ℕ => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n)))
        : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  set K : Submodule ℂ (Lp ℂ 2 μ) := Submodule.span ℂ (Set.range
    (fun n : ℕ => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n))) with hK
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    refine eq_zero_of_inner_coordMonomial_eq_zero hX g fun n => ?_
    have hmem : ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n) ∈ K := by
      rw [hK]
      exact Submodule.subset_span ⟨n, rfl⟩
    have h := (Submodule.mem_orthogonal K g).mp hg _ hmem
    have hconj := congrArg (starRingEnd ℂ) h
    rwa [inner_conj_symm, map_zero] at hconj
  have hclos := Submodule.orthogonal_orthogonal_eq_closure K
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos.symm

/-- **A bounded observable annihilating every monomial vanishes.** -/
theorem eq_zero_of_apply_coordMonomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : C(Ω, ℝ)} (hX : Function.Injective X) (P : Lp ℂ 2 μ →L[ℂ] E)
    (hP : ∀ n : ℕ, P (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n)) = 0) :
    P = 0 := by
  have hspan : ∀ v ∈ Submodule.span ℂ (Set.range
      (fun n : ℕ => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n))), P v = 0 := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨n, rfl⟩
      exact hP n
    · exact map_zero P
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [map_smul, hx, smul_zero]
  have hclosed : IsClosed {v : Lp ℂ 2 μ | P v = 0} :=
    isClosed_eq P.continuous continuous_const
  ext v
  have hmem : v ∈ closure ((Submodule.span ℂ (Set.range
      (fun n : ℕ => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n)))
        : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := dense_span_coordMonomial hX v
  have := hclosed.closure_subset_iff.mpr hspan hmem
  simpa using this

/-- **`(2)`: a nonzero observable has a visible degree.** -/
theorem exists_visible_degree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : C(Ω, ℝ)} (hX : Function.Injective X) (P : Lp ℂ 2 μ →L[ℂ] E) (hP : P ≠ 0) :
    ∃ n : ℕ, P (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X n)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hP (eq_zero_of_apply_coordMonomial hX P hcon)

/-- **`(2)`, parity form.**  An observable that annihilates every odd monomial and is nonzero has a
visible *even* degree. -/
theorem exists_visible_evenDegree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : C(Ω, ℝ)} (hX : Function.Injective X) (P : Lp ℂ 2 μ →L[ℂ] E) (hP : P ≠ 0)
    (hodd : ∀ k : ℕ,
      P (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X (2 * k + 1))) = 0) :
    ∃ k : ℕ, P (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X (2 * k))) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_visible_degree hX P hP
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    exact ⟨k, by rwa [show 2 * k = n by omega]⟩
  · obtain ⟨k, hk⟩ := ho
    exact absurd (by rw [show n = 2 * k + 1 by omega]; exact hodd k) hn

/-- **`(2)`, odd parity form.** -/
theorem exists_visible_oddDegree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : C(Ω, ℝ)} (hX : Function.Injective X) (P : Lp ℂ 2 μ →L[ℂ] E) (hP : P ≠ 0)
    (heven : ∀ k : ℕ,
      P (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X (2 * k))) = 0) :
    ∃ k : ℕ, P (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coordMonomialCM X (2 * k + 1))) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_visible_degree hX P hP
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    exact absurd (by rw [show n = 2 * k by omega]; exact heven k) hn
  · obtain ⟨k, hk⟩ := ho
    exact ⟨k, by rwa [show 2 * k + 1 = n by omega]⟩

end Pairing

end GaloisForLFunctions.HTGeometry
