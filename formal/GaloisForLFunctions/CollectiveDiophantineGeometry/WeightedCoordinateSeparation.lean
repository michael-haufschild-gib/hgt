import GaloisForLFunctions.CollectiveDiophantineGeometry.HereditaryRankBounds
import GaloisForLFunctions.HTGeometry.ReplicaCrowdingSpectralDimensionLaw
import Mathlib.Combinatorics.Hall.Basic

/-!
# Weighted coordinate selection from hereditary rank bounds

A minimum-weight coordinate basis and Hall matching convert hereditary
half-rank bounds into a coordinate subfamily carrying half of any
nonnegative weight and containing no nonzero vector of the given subspace.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Finset
open RHTower.Matveev TranscendenceTheoryOfThePrimeOrbit

set_option autoImplicit false

private theorem exists_normalized_coordinate_basis {k r : ℕ}
    (V : Submodule ℚ (Fin k → ℚ)) (φ : Fin r → Fin k)
    (hr : Module.finrank ℚ V = r)
    (hφ : Set.InjOn (fun v : Fin k → ℚ => fun i => v (φ i)) V) :
    ∃ b : Module.Basis (Fin r) ℚ V,
      ∀ i j, (b i : Fin k → ℚ) (φ j) = if j = i then 1 else 0 := by
  classical
  let f : V →ₗ[ℚ] (Fin r → ℚ) := (LinearMap.funLeft ℚ ℚ φ).comp V.subtype
  have hf : Function.Injective f := by
    intro v w hvw
    exact Subtype.ext (hφ v.property w.property hvw)
  let e : V ≃ₗ[ℚ] (Fin r → ℚ) := f.linearEquivOfInjective hf (by simpa using hr)
  let b := (Pi.basisFun ℚ (Fin r)).map e.symm
  refine ⟨b, fun i j => ?_⟩
  change e (b i) j = _
  rw [Module.Basis.map_apply, e.apply_symm_apply, Pi.basisFun_apply]
  simp only [Pi.single_apply]

private theorem normalized_coordinate_repr {k r : ℕ}
    (V : Submodule ℚ (Fin k → ℚ)) (φ : Fin r → Fin k)
    (b : Module.Basis (Fin r) ℚ V)
    (hb : ∀ i j, (b i : Fin k → ℚ) (φ j) = if j = i then 1 else 0)
    (v : V) (i : Fin r) : b.repr v i = (v : Fin k → ℚ) (φ i) := by
  classical
  have h := congrArg (fun w : V => (w : Fin k → ℚ) (φ i)) (b.sum_repr v)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
    Pi.smul_apply, smul_eq_mul, hb, mul_ite, mul_one, mul_zero] at h
  have hsum : (∑ a, if i = a then b.repr v a else 0) = b.repr v i := by
    calc
      _ = (if i = i then b.repr v i else 0) :=
        Finset.sum_eq_single i (fun a _ ha => if_neg (Ne.symm ha))
          (fun hi => (hi (Finset.mem_univ i)).elim)
      _ = _ := if_pos rfl
  exact hsum.symm.trans h

private theorem normalized_coordinate_injective {k r : ℕ}
    (V : Submodule ℚ (Fin k → ℚ)) (φ : Fin r → Fin k)
    (b : Module.Basis (Fin r) ℚ V)
    (hb : ∀ i j, (b i : Fin k → ℚ) (φ j) = if j = i then 1 else 0) :
    Function.Injective φ := by
  intro i j hij
  by_contra hne
  have h := congrArg (fun a => (b i : Fin k → ℚ) a) hij
  simp only [hb, if_neg (Ne.symm hne)] at h
  exact one_ne_zero h

/-- A nonzero off-pivot coordinate permits exchanging its pivot column. -/
private theorem coordinate_basis_exchange {k r : ℕ}
    (V : Submodule ℚ (Fin k → ℚ)) (φ : Fin r → Fin k)
    (b : Module.Basis (Fin r) ℚ V)
    (hb : ∀ i j, (b i : Fin k → ℚ) (φ j) = if j = i then 1 else 0)
    (i : Fin r) (j : Fin k) (hij : (b i : Fin k → ℚ) j ≠ 0) :
    Set.InjOn (fun v : Fin k → ℚ => fun a => v (Function.update φ i j a)) V := by
  classical
  have hker : ∀ v : V, (∀ a, (v : Fin k → ℚ) (Function.update φ i j a) = 0) → v = 0 := by
    intro v hv
    have hoff : ∀ a, a ≠ i → b.repr v a = 0 := by
      intro a ha
      rw [normalized_coordinate_repr V φ b hb]
      simpa only [Function.update_of_ne ha] using hv a
    have hvj : (v : Fin k → ℚ) j = 0 := by
      simpa only [Function.update_self] using hv i
    have heq : v = b.repr v i • b i := by
      calc
        v = ∑ a, b.repr v a • b a := (b.sum_repr v).symm
        _ = b.repr v i • b i := by
          apply Finset.sum_eq_single i
          · intro a _ ha
            rw [hoff a ha, zero_smul]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    have hmul : b.repr v i * (b i : Fin k → ℚ) j = 0 := by
      have h := congrArg (fun w : V => (w : Fin k → ℚ) j) heq
      simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, hvj] using h.symm
    have hcoeff : b.repr v i = 0 := (mul_eq_zero.mp hmul).resolve_right hij
    exact heq.trans (by rw [hcoeff, zero_smul])
  intro v hv w hw heq
  let z : V := ⟨v - w, V.sub_mem hv hw⟩
  have hz : z = 0 := hker z (fun a => sub_eq_zero.mpr (congrFun heq a))
  exact sub_eq_zero.mp (congrArg (fun z : V => (z : Fin k → ℚ)) hz)

/-- Hereditary half-rank gives Hall's condition for the non-pivot supports
of every normalized coordinate basis. -/
private theorem exists_coordinate_basis_matching {k r : ℕ}
    (V : Submodule ℚ (Fin k → ℚ)) (φ : Fin r → Fin k)
    (b : Module.Basis (Fin r) ℚ V)
    (hb : ∀ i j, (b i : Fin k → ℚ) (φ j) = if j = i then 1 else 0)
    (hV : ∀ J : Finset (Fin k),
      2 * Module.finrank ℚ ↥(V ⊓ coordinateSubspace J) ≤ J.card) :
    ∃ μ : Fin r → Fin k, Function.Injective μ ∧
      ∀ i, μ i ∉ univ.image φ ∧ (b i : Fin k → ℚ) (μ i) ≠ 0 := by
  classical
  let N : Fin r → Finset (Fin k) := fun i =>
    univ.filter fun j => j ∉ univ.image φ ∧ (b i : Fin k → ℚ) j ≠ 0
  have hφ := normalized_coordinate_injective V φ b hb
  have hbind : LinearIndependent ℚ (fun i => (b i : Fin k → ℚ)) :=
    b.linearIndependent.map' V.subtype V.ker_subtype
  have hHall : ∀ A : Finset (Fin r), A.card ≤ (A.biUnion N).card := by
    intro A
    let vA : A → Fin k → ℚ := fun i => (b (i : Fin r) : Fin k → ℚ)
    let U := Submodule.span ℚ (Set.range vA)
    let K := A.image φ ∪ A.biUnion N
    have hdim : Module.finrank ℚ U = A.card := by
      have hindA : LinearIndependent ℚ vA :=
        hbind.comp (Subtype.val : A → Fin r) Subtype.val_injective
      exact (finrank_span_eq_card hindA).trans (Fintype.card_coe A)
    have hUK : U ≤ V ⊓ coordinateSubspace K := by
      apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      refine ⟨(b i).property, ?_⟩
      intro j hj
      by_contra hne
      change (b i : Fin k → ℚ) j ≠ 0 at hne
      apply hj
      change j ∈ A.image φ ∪ A.biUnion N
      by_cases hI : j ∈ univ.image φ
      · obtain ⟨a, -, haj⟩ := Finset.mem_image.mp hI
        have hai : a = (i : Fin r) := by
          by_contra hai
          apply hne
          rw [← haj, hb, if_neg hai]
        subst a
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, i.property, haj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i, i.property, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hI, hne⟩⟩)
    have hdisj : Disjoint (A.image φ) (A.biUnion N) := by
      apply Finset.disjoint_left.mpr
      intro j hj hN
      obtain ⟨a, -, haj⟩ := Finset.mem_image.mp hj
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hN
      exact (Finset.mem_filter.mp hi).2.1 (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, haj⟩)
    have hcard : K.card = A.card + (A.biUnion N).card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hφ]
    have hdimle := Submodule.finrank_mono hUK
    rw [hdim] at hdimle
    have hbound := hV K
    rw [hcard] at hbound
    omega
  obtain ⟨μ, hμ, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨μ, hμ, fun i => (Finset.mem_filter.mp (hmem i)).2⟩

/-- Hereditary half-rank leaves a coordinate set of at least half the total
nonnegative weight on which the subspace has no nonzero supported vector. -/
theorem exists_half_weight_avoiding_subspace {k : ℕ}
    (V : Submodule ℚ (Fin k → ℚ))
    (hV : ∀ J : Finset (Fin k),
      2 * Module.finrank ℚ ↥(V ⊓ coordinateSubspace J) ≤ J.card)
    (w : Fin k → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∃ J : Finset (Fin k), (∑ j, w j) ≤ 2 * ∑ j ∈ J, w j ∧
      V ⊓ coordinateSubspace J = ⊥ := by
  classical
  let r := Module.finrank ℚ V
  let P : Finset (Fin r → Fin k) := univ.filter fun φ =>
    Set.InjOn (fun v : Fin k → ℚ => fun i => v (φ i)) V
  obtain ⟨φ₀, hφ₀⟩ := HTGeometry.exists_coordinateProjection_injective_on_submodule V
  have hP : P.Nonempty := ⟨φ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ₀⟩⟩
  obtain ⟨φ, hφP, hmin⟩ := Finset.exists_min_image P (fun φ => ∑ i, w (φ i)) hP
  have hφ := (Finset.mem_filter.mp hφP).2
  obtain ⟨b, hb⟩ := exists_normalized_coordinate_basis V φ rfl hφ
  have hφinj := normalized_coordinate_injective V φ b hb
  have hcost : ∀ i j, (b i : Fin k → ℚ) j ≠ 0 → w (φ i) ≤ w j := by
    intro i j hij
    have hswap := coordinate_basis_exchange V φ b hb i j hij
    have hm := hmin (Function.update φ i j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hswap⟩)
    have hsum : (∑ a, w (Function.update φ i j a)) =
        (∑ a, w (φ a)) + (w j - w (φ i)) := by
      calc
        _ = ∑ a, (w (φ a) + if a = i then w j - w (φ i) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : a = i
          · subst a
            simp
          · simp only [Function.update_of_ne ha, if_neg ha, add_zero]
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [hsum] at hm
    linarith only [hm]
  obtain ⟨μ, hμ, hμmem⟩ := exists_coordinate_basis_matching V φ b hb hV
  let I := univ.image φ
  let J := Iᶜ
  have hI : (∑ j ∈ I, w j) = ∑ i, w (φ i) :=
    Finset.sum_image (fun _ _ _ _ h => hφinj h)
  have hμsub : univ.image μ ⊆ J := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_compl.mpr (hμmem i).1
  have hweight : (∑ j ∈ I, w j) ≤ ∑ j ∈ J, w j := by
    rw [hI]
    calc
      _ ≤ ∑ i, w (μ i) := Finset.sum_le_sum fun i _ => hcost i (μ i) (hμmem i).2
      _ = ∑ j ∈ univ.image μ, w j := (Finset.sum_image (fun _ _ _ _ h => hμ h)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hμsub (fun j _ _ => hw j)
  have hdisj : Disjoint I J := Finset.disjoint_left.mpr
    (fun j hj hJ => Finset.mem_compl.mp hJ hj)
  have hunion : I ∪ J = univ := by ext j; simp [J]
  have htotal : (∑ j ∈ I, w j) + (∑ j ∈ J, w j) = ∑ j, w j := by
    rw [← Finset.sum_union hdisj, hunion]
  refine ⟨J, by linarith only [hweight, htotal], ?_⟩
  apply bot_unique
  intro v hv
  change v = 0
  apply hφ hv.1 V.zero_mem
  ext i
  apply hv.2 (φ i)
  intro hi
  exact Finset.mem_compl.mp hi (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- At least half of any nonnegative prime weight survives on a coordinate
subfamily whose nonzero height-`H` forms satisfy the explicit separation floor. -/
theorem exists_weighted_prime_coordinate_separation {k : ℕ}
    (p : Fin (k + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    {H : ℝ} (hH : 1 ≤ H) (w : Fin (k + 1) → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∃ J : Finset (Fin (k + 1)), (∑ j, w j) ≤ 2 * ∑ j ∈ J, w j ∧
      ∀ v : Fin (k + 1) → ℤ, (∀ j, j ∉ J → v j = 0) →
        (∀ j, |(v j : ℝ)| ≤ H) → v ≠ 0 →
        hereditaryDepthFloor (k + 1) (collectiveLogBound p) H ≤ |primeLogForm p v| := by
  classical
  let δ := hereditaryDepthFloor (k + 1) (collectiveLogBound p) H
  let S := (nearRelationBox p ⌈H⌉₊ δ).filter fun v => ∀ j, |(v j : ℝ)| ≤ H
  have hheight : ∀ v ∈ S, ∀ j, |(v j : ℝ)| ≤ H := fun v hv =>
    (Finset.mem_filter.mp hv).2
  have hsmall : ∀ v ∈ S, |primeLogForm p v| < δ := fun v hv =>
    ((mem_nearRelationBox p ⌈H⌉₊ δ v).mp (Finset.mem_filter.mp hv).1).2
  have hhered := hereditary_small_forms_finrank_le p hp hprime S hH hheight hsmall
  obtain ⟨J, hweight, havoid⟩ := exists_half_weight_avoiding_subspace (integerRowSpan S) hhered w hw
  refine ⟨J, hweight, ?_⟩
  intro v hsupp hv hne
  by_contra hlarge
  have hSv : v ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨(mem_nearRelationBox p ⌈H⌉₊ δ v).mpr ⟨?_, lt_of_not_ge hlarge⟩, hv⟩
    intro j
    exact_mod_cast (hv j).trans (Nat.le_ceil H)
  have hmem : (fun j => (v j : ℚ)) ∈ integerRowSpan S ⊓ coordinateSubspace J := by
    refine ⟨Submodule.subset_span ⟨v, hSv, rfl⟩, ?_⟩
    intro j hj
    change (v j : ℚ) = 0
    rw [hsupp j hj, Int.cast_zero]
  rw [havoid] at hmem
  have hz : (fun j => (v j : ℚ)) = 0 := hmem
  apply hne
  ext j
  have h := congrFun hz j
  change (v j : ℚ) = 0 at h
  change v j = 0
  exact_mod_cast h

end GaloisForLFunctions.CollectiveDiophantineGeometry
