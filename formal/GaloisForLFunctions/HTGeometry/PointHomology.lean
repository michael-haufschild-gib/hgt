import GaloisForLFunctions.HTGeometry.HomotopyInvariance
import GaloisForLFunctions.HTGeometry.SmallQuasiIso

/-!
# The homology of a point, and of a contractible space

A singular simplex whose image is a single point is the constant simplex, so the chains supported in
a point are free of rank one in each degree and the boundary is multiplication by the alternating
sum `∑_{i<n+1} (-1)^i`, which is `1` in odd degrees and `0` in even ones.  The complex is therefore
exact in every positive degree.

A space that is homotopy equivalent to a point has the identity of its homology factoring through
the homology of that point, so all of its positive-degree homology vanishes.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The constant singular simplex at a point. -/
noncomputable def constSimplex (x : X) (k : ℕ) : C(topSimplex k, X) :=
  ContinuousMap.const _ x

theorem eq_constSimplex {x : X} {k : ℕ} {σ : C(topSimplex k, X)}
    (h : Set.range σ ⊆ ({x} : Set X)) : σ = constSimplex x k :=
  ContinuousMap.ext fun y => h ⟨y, rfl⟩

theorem constSimplex_comp {x : X} {k m : ℕ} (f : Fin (k + 1) → Fin (m + 1)) :
    (constSimplex x m).comp (topMap f) = constSimplex x k := rfl

theorem sum_neg_one_pow_fin (m : ℕ) :
    (∑ i : Fin m, (-1 : R) ^ (i : ℕ)) = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    rcases Nat.even_or_odd m with hm | hm
    · have h1 : ¬ Even (m + 1) := by simp [Nat.even_add_one, hm]
      rw [if_pos hm, hm.neg_one_pow, zero_add, if_neg h1]
    · have h0 : ¬ Even m := by simp [Nat.not_even_iff_odd, hm]
      have h1 : Even (m + 1) := by simp [Nat.even_add_one, h0]
      rw [if_neg h0, hm.neg_one_pow, add_neg_cancel, if_pos h1]

theorem mem_subChains_singleton {x : X} {k : ℕ} {c : C(topSimplex k, X) →₀ R}
    (hc : c ∈ subChains R ({x} : Set X) k) :
    c = Finsupp.single (constSimplex x k) (c (constSimplex x k)) := by
  classical
  rw [mem_subChains] at hc
  refine Finsupp.ext fun σ => ?_
  by_cases hσ : σ ∈ c.support
  · rw [eq_constSimplex (hc σ hσ), Finsupp.single_eq_same]
  · by_cases hcs : σ = constSimplex x k
    · rw [hcs, Finsupp.single_eq_same, ← hcs]
    · rw [Finsupp.notMem_support_iff.mp hσ, Finsupp.single_eq_of_ne hcs]

theorem singBd_single_const {x : X} {k : ℕ} (r : R) :
    singBd R X k (Finsupp.single (constSimplex x (k + 1)) r)
      = Finsupp.single (constSimplex x k) (r * ∑ i : Fin (k + 2), (-1 : R) ^ (i : ℕ)) := by
  have hsm : Finsupp.single (constSimplex x (k + 1)) r
      = r • Finsupp.single (constSimplex x (k + 1)) (1 : R) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsm, map_smul, singBd_single]
  have hterm : ∀ i : Fin (k + 2),
      Finsupp.single ((constSimplex x (k + 1)).comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ))
        = Finsupp.single (constSimplex x k) ((-1 : R) ^ (i : ℕ)) := by
    intro i
    rw [constSimplex_comp]
  have hsum : (∑ i : Fin (k + 2), Finsupp.single (constSimplex x k) ((-1 : R) ^ (i : ℕ)))
      = Finsupp.single (constSimplex x k) (∑ i : Fin (k + 2), (-1 : R) ^ (i : ℕ)) := by
    classical
    refine Finsupp.ext fun σ => ?_
    rw [Finset.sum_apply']
    by_cases h : σ = constSimplex x k
    · subst h
      simp
    · simp [Finsupp.single_eq_of_ne h]
  rw [Finset.sum_congr rfl fun i _ => hterm i, hsum, Finsupp.smul_single, smul_eq_mul]

/-! ### The homology of a one-point space -/

instance uniqueSimplexOfUnique (P : Type v) [TopologicalSpace P] [Unique P] (m : ℕ) :
    Unique (C(topSimplex m, P)) where
  default := ContinuousMap.const _ default
  uniq _ := ContinuousMap.ext fun _ => Subsingleton.elim _ _

theorem finsupp_unique_eq {α : Type*} [Unique α] (c : α →₀ R) :
    c = Finsupp.single default (c default) := by
  refine Finsupp.ext fun a => ?_
  rw [Unique.eq_default a, Finsupp.single_eq_same]

theorem singBd_single_default (P : Type v) [TopologicalSpace P] [Unique P] (k : ℕ) (r : R) :
    singBd R P k (Finsupp.single default r)
      = Finsupp.single (default : C(topSimplex k, P))
        (r * ∑ i : Fin (k + 2), (-1 : R) ^ (i : ℕ)) := by
  classical
  have hsm : Finsupp.single (default : C(topSimplex (k + 1), P)) r
      = r • Finsupp.single (default : C(topSimplex (k + 1), P)) (1 : R) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsm, map_smul, singBd_single]
  have hterm : ∀ i : Fin (k + 2),
      Finsupp.single
          ((default : C(topSimplex (k + 1), P)).comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ))
        = Finsupp.single (default : C(topSimplex k, P)) ((-1 : R) ^ (i : ℕ)) := by
    intro i
    rw [Unique.eq_default ((default : C(topSimplex (k + 1), P)).comp (topMap i.succAbove))]
  have hsum : (∑ i : Fin (k + 2),
        Finsupp.single (default : C(topSimplex k, P)) ((-1 : R) ^ (i : ℕ)))
      = Finsupp.single (default : C(topSimplex k, P)) (∑ i : Fin (k + 2), (-1 : R) ^ (i : ℕ)) := by
    refine Finsupp.ext fun σ => ?_
    rw [Finset.sum_apply']
    rw [Unique.eq_default σ]
    simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, hsum, Finsupp.smul_single, smul_eq_mul]

/-- **The singular chain complex of a one-point space is exact in every positive degree.** -/
theorem exactAt_singChainComplex_of_unique (P : Type v) [TopologicalSpace P] [Unique P] (k : ℕ) :
    (singChainComplex R P).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ k),
    ShortComplex.moduleCat_exact_iff]
  intro y hy
  obtain ⟨c, rfl⟩ : ∃ c : C(topSimplex (k + 1), P) →₀ R, c = y := ⟨y, rfl⟩
  have hg : ∀ c : C(topSimplex (k + 1), P) →₀ R,
      ((HomologicalComplex.sc' (singChainComplex R P) (k + 2) (k + 1) k).g) c
        = singBd R P k c := fun _ => rfl
  have hf : ∀ c : C(topSimplex (k + 2), P) →₀ R,
      ((HomologicalComplex.sc' (singChainComplex R P) (k + 2) (k + 1) k).f) c
        = singBd R P (k + 1) c := fun _ => rfl
  set r : R := c default with hr
  have hrep : c = Finsupp.single (default : C(topSimplex (k + 1), P)) r := finsupp_unique_eq R c
  rw [hg c] at hy
  by_cases hk : Even (k + 2)
  · refine ⟨Finsupp.single (default : C(topSimplex (k + 2), P)) r, ?_⟩
    have hodd : ¬ Even (k + 3) := by
      simp only [Nat.even_add_one] at hk ⊢
      simpa using hk
    rw [hf, singBd_single_default, sum_neg_one_pow_fin, if_neg hodd, mul_one, hrep]
  · have hone : (∑ i : Fin (k + 2), (-1 : R) ^ (i : ℕ)) = 1 := by
      rw [sum_neg_one_pow_fin, if_neg hk]
    rw [hrep, singBd_single_default, hone, mul_one] at hy
    have hr0 : r = 0 := by
      have h2 : Finsupp.single (default : C(topSimplex k, P)) r
          = (0 : C(topSimplex k, P) →₀ R) := hy
      have h3 := congrArg (fun d : C(topSimplex k, P) →₀ R => d default) h2
      simpa using h3
    refine ⟨(0 : C(topSimplex (k + 2), P) →₀ R), ?_⟩
    rw [hf, map_zero, hrep, hr0, Finsupp.single_zero]

/-! ### Contractible spaces -/

/-- The one-point space, as a target for constant maps. -/
noncomputable def toPUnit (X : Type v) [TopologicalSpace X] : C(X, PUnit.{v + 1}) :=
  ContinuousMap.const _ PUnit.unit

/-- The inclusion of a point. -/
noncomputable def fromPUnit (x : X) : C(PUnit.{v + 1}, X) :=
  ContinuousMap.const _ x

theorem fromPUnit_comp_toPUnit (x : X) :
    (fromPUnit x).comp (toPUnit X) = ContinuousMap.const X x := rfl

/-- **A space contractible to a point has no homology in positive degrees.** -/
theorem isZero_homology_of_homotopy_const {x : X}
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X x)) (k : ℕ) :
    IsZero ((singChainComplex R X).homology (k + 1)) := by
  have h1 := homologyMap_singMap_eq_of_homotopy R H (k + 1)
  rw [singMap_id, HomologicalComplex.homologyMap_id, ← fromPUnit_comp_toPUnit x,
    singMap_comp, HomologicalComplex.homologyMap_comp] at h1
  have hz : IsZero ((singChainComplex R PUnit.{v + 1}).homology (k + 1)) :=
    (exactAt_singChainComplex_of_unique R PUnit.{v + 1} k).isZero_homology
  rw [IsZero.iff_id_eq_zero, h1,
    hz.eq_zero_of_tgt (HomologicalComplex.homologyMap (singMap R (toPUnit X)) (k + 1)),
    Limits.zero_comp]

end GaloisForLFunctions.HTGeometry
