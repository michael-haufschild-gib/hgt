import GaloisForLFunctions.HTGeometry.RatFuncCoordinateScaling
import GaloisForLFunctions.HTGeometry.IndefiniteSumDifferentialDependence
import GaloisForLFunctions.HTGeometry.ShiftedDigammaFamilyIndependence
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect

/-!
# The atomic scaled-digamma theorem

Let `ω ≠ 0` and let `y₁,…,y_r` be elements of the global meromorphic differential field whose
translation defects by `ω` are the simple poles

```text
σ_ω(yᵢ) - yᵢ = 1/(X + bᵢ),
```

with the `bᵢ` pairwise incongruent modulo `ωℤ`.  A differential relation among the `yᵢ` over `ℂ(X)`
would, by the descent, produce constants `a_{i,j}` not all zero, fixed by the shift — hence complex
numbers — and a rational `g` with

```text
∑_{i,j} a_{i,j} · d^j/dX^j (1/(X + bᵢ)) = g(X + ω) - g(X).
```

Dilating the coordinate by `ω` turns this into the unit-shift statement for the poles `bᵢ/ω`, which
are pairwise incongruent modulo `ℤ`; the orbit-residue theorem forbids it.  Hence the `yᵢ` are
differentially independent.

Applied to the translates of one solution of the order-one Barnes ladder `σ_ω φ - φ = 1/X`, this is
the atomic differential independence of the scaled-digamma translates: for shifts pairwise distinct
modulo `ωℤ`, the translates `φ(z + h)` are differentially algebraically independent over `ℂ(z)`.
-/

open scoped BigOperators Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase

/-! ## The scaled shift of a simple pole -/

theorem ratShiftBy_ratFuncX (q : ℂ) :
    ratShiftBy q RatFunc.X = RatFunc.X + RatFunc.C q := by
  rw [← RatFunc.algebraMap_X, ratShiftBy_algebraMap, Polynomial.X_comp, map_add,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem ratShiftBy_one_div_X (q : ℂ) :
    ratShiftBy q (1 / RatFunc.X) = 1 / (RatFunc.X + RatFunc.C q) := by
  rw [map_div₀, map_one, ratShiftBy_ratFuncX]

theorem ratShiftBy_ratFuncC (q t : ℂ) : ratShiftBy q (RatFunc.C t) = RatFunc.C t := by
  rw [← RatFunc.algebraMap_C, ratShiftBy_algebraMap, Polynomial.C_comp]

theorem ratShiftBy_one_div_X_add_C (q b : ℂ) :
    ratShiftBy q (1 / (RatFunc.X + RatFunc.C b)) = 1 / (RatFunc.X + RatFunc.C (b + q)) := by
  rw [map_div₀, map_one, map_add, ratShiftBy_ratFuncX, ratShiftBy_ratFuncC]
  congr 1
  rw [map_add]
  ring

/-! ## Differential independence from simple-pole defects -/

/-- **Simple-pole defects on distinct orbits give differential independence.**  Elements of the
global meromorphic differential field whose `ω`-translation defects are the simple poles
`1/(X + bᵢ)` with the `bᵢ` pairwise incongruent modulo `ωℤ` are differentially independent over
`ℂ(X)`. -/
theorem differentialIndependent_of_shiftDefect_simplePole {ω : ℂ} (hω : ω ≠ 0) {r : ℕ}
    (b : Fin r → ℂ) (hincong : ∀ i i' : Fin r, i ≠ i' → ∀ n : ℤ, b i - b i' ≠ (n : ℂ) * ω)
    (y : Fin r → meroField (Set.univ : Set ℂ))
    (hy : ∀ i, addTranslationMeroEquiv ω (y i)
      = y i + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C (b i)))) :
    DifferentialIndependent (RatFunc ℂ) y := by
  classical
  by_contra hdep
  obtain ⟨s, a, g, ⟨p₀, hp₀s, hp₀⟩, hinv, hsum⟩ :=
    exists_telescoper_of_not_differentialIndependent
      (K := RatFunc ℂ) (L := meroField (Set.univ : Set ℂ))
      (ratShiftBy ω) (addTranslationMeroEquiv ω)
      (fun x => addTranslationMeroEquiv_deriv ω x)
      (fun c => addTranslationMeroEquiv_ratfuncToMero_by ω c)
      y (fun i => 1 / (RatFunc.X + RatFunc.C (b i)))
      (fun i => by rw [hy i]; ring) hdep
  choose t ht using fun p : Fin r × ℕ => ratShiftBy_fixed_eq_const hω (hinv p)
  set N : ℕ := s.sup (fun p => p.2) with hN
  set delta : Fin r → Fin (N + 1) → ℂ :=
    fun i j => if (i, (j : ℕ)) ∈ s then t (i, (j : ℕ)) else 0 with hdelta
  set G : Fin r × ℕ → RatFunc ℂ :=
    fun q => algebraMap ℂ (RatFunc ℂ) (if q ∈ s then t q else 0) *
      familyIncrement b q.1 q.2 with hG
  set e : Fin r × Fin (N + 1) → Fin r × ℕ := fun x => (x.1, (x.2 : ℕ)) with he
  have heinj : Function.Injective e := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hx
    simp only [he, Prod.mk.injEq] at hx
    exact Prod.ext hx.1 (Fin.ext hx.2)
  have hmemN : ∀ p ∈ s, p.2 < N + 1 := by
    intro p hp
    have : p.2 ≤ N := by
      rw [hN]
      exact Finset.le_sup (f := fun q : Fin r × ℕ => q.2) hp
    omega
  have hsub : s ⊆ Finset.image e Finset.univ := by
    intro p hp
    refine Finset.mem_image.mpr ⟨(p.1, ⟨p.2, hmemN p hp⟩), Finset.mem_univ _, ?_⟩
    simp [he]
  have hoff : ∀ q ∈ Finset.image e Finset.univ, q ∉ s → G q = 0 := by
    intro q _ hq
    rw [hG]
    simp only [if_neg hq, map_zero, zero_mul]
  have hpad : ∑ i : Fin r, ∑ j : Fin (N + 1),
      algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement b i (j : ℕ)
      = ∑ p ∈ s, a p * differentialJet p.2 (1 / (RatFunc.X + RatFunc.C (b p.1))) := by
    have hleft : ∑ i : Fin r, ∑ j : Fin (N + 1),
        algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement b i (j : ℕ)
        = ∑ x : Fin r × Fin (N + 1), G (e x) := by
      rw [← Finset.sum_product']
      exact Finset.sum_congr rfl fun x _ => rfl
    have himage : ∑ x : Fin r × Fin (N + 1), G (e x)
        = ∑ q ∈ Finset.image e Finset.univ, G q :=
      (Finset.sum_image fun x _ x' _ hxx => heinj hxx).symm
    rw [hleft, himage, ← Finset.sum_subset hsub hoff]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hG]
    simp only [if_pos hp]
    rw [← ht p, differentialJet_one_div_shift b p.1 p.2]
  have hcomb : ratShiftBy ω g - g = ∑ i : Fin r, ∑ j : Fin (N + 1),
      algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement b i (j : ℕ) := by
    rw [hpad, hsum]
  have hzero := ratShiftBy_sub_familyIncrement_combination hω b hincong hcomb
  have hp₀t : t p₀ ≠ 0 := by
    intro hcon
    rw [ht p₀, hcon, map_zero] at hp₀
    exact hp₀ rfl
  refine hp₀t ?_
  have := hzero p₀.1 ⟨p₀.2, hmemN p₀ hp₀s⟩
  rw [hdelta] at this
  simpa [if_pos hp₀s] using this

/-! ## The atomic scaled-digamma theorem -/

/-- **The atomic scaled-digamma theorem.**  If `φ` solves the order-one ladder equation
`φ(z + ω) - φ(z) = 1/z` in the global meromorphic differential field, then its translates through
shifts pairwise distinct modulo `ωℤ` are differentially algebraically independent over `ℂ(z)`.

For `φ = Ψ₁(·|ω)` this is the atomic step of the Barnes translation-annihilator theorem: no nonzero
constant-coefficient differential-linear form in such translates is differentially algebraic. -/
theorem differentialIndependent_ladderTranslate {ω : ℂ} (hω : ω ≠ 0) (b : ℂ)
    (φ : meroField (Set.univ : Set ℂ))
    (hφ : addTranslationMeroEquiv ω φ
      = φ + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C b)))
    {r : ℕ} (h : Fin r → ℂ)
    (hincong : ∀ i i' : Fin r, i ≠ i' → ∀ n : ℤ, h i - h i' ≠ (n : ℂ) * ω) :
    DifferentialIndependent (RatFunc ℂ) fun i => addTranslationMeroEquiv (h i) φ := by
  have hincong' : ∀ i i' : Fin r, i ≠ i' → ∀ n : ℤ,
      (b + h i) - (b + h i') ≠ (n : ℂ) * ω := by
    intro i i' hii n hcon
    exact hincong i i' hii n (by linear_combination hcon)
  refine differentialIndependent_of_shiftDefect_simplePole hω (fun i => b + h i) hincong' _
    fun i => ?_
  have halg : ∀ q : RatFunc ℂ, algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) q
      = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ q := fun _ => rfl
  have hcomm : addTranslationMeroEquiv ω (addTranslationMeroEquiv (h i) φ)
      = addTranslationMeroEquiv (h i) (addTranslationMeroEquiv ω φ) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  rw [hcomm, hφ, (addTranslationMeroEquiv (h i)).map_add]
  simp only [halg]
  rw [addTranslationMeroEquiv_ratfuncToMero_by, ratShiftBy_one_div_X_add_C]

end

end GaloisForLFunctions.HTGeometry

/-! ## An arbitrary finite index -/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase

/-- **The atomic scaled-digamma theorem for an arbitrary finite index.**  Reindexing along a
bijection with a standard finite type preserves differential independence. -/
theorem differentialIndependent_ladderTranslate_fintype {ω : ℂ} (hω : ω ≠ 0) (b : ℂ)
    (φ : meroField (Set.univ : Set ℂ))
    (hφ : addTranslationMeroEquiv ω φ
      = φ + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C b)))
    {κ : Type*} [Fintype κ] (h : κ → ℂ)
    (hincong : ∀ i i' : κ, i ≠ i' → ∀ n : ℤ, h i - h i' ≠ (n : ℂ) * ω) :
    DifferentialIndependent (RatFunc ℂ) fun i => addTranslationMeroEquiv (h i) φ := by
  classical
  set e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ with he
  have hincong' : ∀ m m' : Fin (Fintype.card κ), m ≠ m' →
      ∀ n : ℤ, h (e.symm m) - h (e.symm m') ≠ (n : ℂ) * ω := by
    intro m m' hmm n
    refine hincong _ _ (fun hc => hmm ?_) n
    rw [← e.apply_symm_apply m, ← e.apply_symm_apply m', hc]
  have hbase :=
    differentialIndependent_ladderTranslate hω b φ hφ (fun m => h (e.symm m)) hincong'
  have hcomp := hbase.comp e e.injective
  have hfun : ((fun m => addTranslationMeroEquiv (h (e.symm m)) φ) ∘ e)
      = fun i => addTranslationMeroEquiv (h i) φ := by
    funext i
    simp only [Function.comp_apply, he, Equiv.symm_apply_apply]
  rwa [hfun] at hcomp

end

end GaloisForLFunctions.HTGeometry
