import GaloisForLFunctions.BiarithmeticGeometry.Affine.IsotropicTranslations
import GaloisForLFunctions.HeckeKreinToeplitz.Index.NilpotentSubspaces

/-!
# Finite affine orbits of translation-period defects

A periodic translation reading makes its column differences isotropic. Their affine
orbit retains a uniform translation nilpotence exponent. The fixed kernel is again
isotropic, so finite negative index bounds the entire defect space by its square.
-/

open Complex Module
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The failure of a kernel column to retain one integer translation period. -/
def translationPeriodDefect (k : AffineGroupQ → ℂ) (q : ℚ) : kernelColumnSpan k :=
  kernelColumnPoint k (translation (q + 1)) - kernelColumnPoint k (translation q)

/-- Translation-period defects retain their mixed values on the whole affine group. -/
def translationPeriodSpace (k : AffineGroupQ → ℂ) : Submodule ℂ (kernelColumnSpan k) :=
  Submodule.span ℂ (Set.range (translationPeriodDefect k))

theorem translationPeriodDefect_translate (k : AffineGroupQ → ℂ) (b q : ℚ) :
    kernelColumnRepresentation k (translation b) (translationPeriodDefect k q) =
      translationPeriodDefect k (b + q) := by
  apply Subtype.ext
  funext g
  change k (((translation b)⁻¹ * g)⁻¹ * translation (q + 1)) -
      k (((translation b)⁻¹ * g)⁻¹ * translation q) =
    k (g⁻¹ * translation (b + q + 1)) - k (g⁻¹ * translation (b + q))
  rw [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_assoc, ← translation_add, ← translation_add,
    show b + (q + 1) = b + q + 1 by ring]

theorem translationPeriodSpace_invariant (k : AffineGroupQ → ℂ) (b : ℚ) :
    Set.MapsTo (kernelColumnRepresentation k (translation b))
      (translationPeriodSpace k) (translationPeriodSpace k) := by
  intro x hx
  change kernelColumnRepresentation k (translation b) x ∈ translationPeriodSpace k
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      rw [translationPeriodDefect_translate]
      exact Submodule.subset_span ⟨b + q, rfl⟩
  | zero => simpa only [map_zero] using (translationPeriodSpace k).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (translationPeriodSpace k).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (translationPeriodSpace k).smul_mem c ih

/-- Periodicity of the translation reading makes all period defects mutually isotropic. -/
theorem translationPeriodSpace_isotropic {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) :
    ∀ x ∈ translationPeriodSpace k, ∀ y ∈ translationPeriodSpace k,
      kernelColumnPairing k x y = 0 := by
  have hbase (a b : ℚ) : kernelColumnPairing k (kernelColumnPoint k (translation a))
      (translationPeriodDefect k b) = 0 := by
    rw [kernelColumnPairing_point_left hk]
    change k ((translation a)⁻¹ * translation (b + 1)) -
      k ((translation a)⁻¹ * translation b) = 0
    rw [translation_inv_mul, translation_inv_mul,
      show b + 1 - a = (b - a) + 1 by ring, hper, sub_self]
  have hpair (a b : ℚ) : kernelColumnPairing k (translationPeriodDefect k a)
      (translationPeriodDefect k b) = 0 := by
    have he : translationPeriodDefect k a = kernelColumnPoint k (translation (a + 1)) +
        (-1 : ℂ) • kernelColumnPoint k (translation a) := by
      apply Subtype.ext
      funext g
      change k (g⁻¹ * translation (a + 1)) - k (g⁻¹ * translation a) =
        k (g⁻¹ * translation (a + 1)) + (-1 : ℂ) * k (g⁻¹ * translation a)
      ring
    rw [he, kernelColumnPairing_add_left hk, kernelColumnPairing_smul_left hk,
      hbase, hbase, mul_zero, add_zero]
  have hker (a : ℚ) : translationPeriodSpace k ≤
      LinearMap.ker (kernelColumnPairing k (translationPeriodDefect k a)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨b, rfl⟩
    exact hpair a b
  intro x hx y hy
  have hyker : translationPeriodSpace k ≤ LinearMap.ker (kernelColumnPairing k y) := by
    apply Submodule.span_le.mpr
    rintro z ⟨a, rfl⟩
    change kernelColumnPairing k y (translationPeriodDefect k a) = 0
    rw [kernelColumnPairing_conj_symm hk,
      show kernelColumnPairing k (translationPeriodDefect k a) y = 0 from hker a hy, map_zero]
  rw [kernelColumnPairing_conj_symm hk, show kernelColumnPairing k y x = 0 from hyker hx,
    map_zero]

theorem finite_translationPeriodSpace {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) :
    Module.Finite ℂ (translationPeriodSpace k) ∧
      Module.finrank ℂ (translationPeriodSpace k) ≤ r :=
  finite_isotropic_column_subspace hk hi (translationPeriodSpace k)
    (translationPeriodSpace_isotropic hk hper)

/-- The negative index bounds the unipotence exponent on all period defects. -/
theorem translationPeriodSpace_unipotent {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) (b : ℚ)
    (v : kernelColumnSpan k) (hv : v ∈ translationPeriodSpace k) :
    (translationColumnDifference k b ^ r) v = 0 :=
  isotropic_translation_difference_pow_apply hk hi (translationPeriodSpace k)
    (translationPeriodSpace_isotropic hk hper) (translationPeriodSpace_invariant k) b
    v hv

/-- The integer Haar successor has period one on the rational translation subgroup. -/
theorem hasIntegerSuccessor_translation_periodic {k : AffineGroupQ → ℂ}
    (hs : HasIntegerSuccessor k) (b : ℚ) : k (translation (b + 1)) = k (translation b) := by
  have hden : (b + 1).den = 1 ↔ b.den = 1 := by
    rw [den_eq_one_iff_exists, den_eq_one_iff_exists]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩
      push_cast
      linarith only [hm]
    · rintro ⟨m, hm⟩
      refine ⟨m + 1, ?_⟩
      push_cast
      linarith only [hm]
  rw [hs (b + 1), hs b]
  simp only [hden]

/-- The affine orbit of one period defect generates every translated period defect. -/
def affinePeriodSpace (k : AffineGroupQ → ℂ) : Submodule ℂ (kernelColumnSpan k) :=
  Submodule.span ℂ (Set.range fun g =>
    kernelColumnRepresentation k g (translationPeriodDefect k 0))

theorem affinePeriodSpace_invariant (k : AffineGroupQ → ℂ) (g : AffineGroupQ) :
    Set.MapsTo (kernelColumnRepresentation k g) (affinePeriodSpace k) (affinePeriodSpace k) := by
  intro x hx
  change kernelColumnRepresentation k g x ∈ affinePeriodSpace k
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have he : kernelColumnRepresentation k g
          (kernelColumnRepresentation k h (translationPeriodDefect k 0)) =
          kernelColumnRepresentation k (g * h) (translationPeriodDefect k 0) := by
        rw [map_mul, Module.End.mul_apply]
      rw [he]
      exact Submodule.subset_span ⟨g * h, rfl⟩
  | zero => simpa only [map_zero] using (affinePeriodSpace k).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (affinePeriodSpace k).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (affinePeriodSpace k).smul_mem c ih

theorem translationPeriodSpace_le_affinePeriodSpace (k : AffineGroupQ → ℂ) :
    translationPeriodSpace k ≤ affinePeriodSpace k := by
  apply Submodule.span_le.mpr
  rintro x ⟨q, rfl⟩
  have he := translationPeriodDefect_translate k q 0
  rw [add_zero] at he
  rw [← he]
  exact Submodule.subset_span ⟨translation q, rfl⟩

private theorem translation_mul_affine (g : AffineGroupQ) (b : ℚ) :
    translation b * g = g * translation (b / affSlope g) := by
  apply affine_ext
  · simp only [affSlope_mul, affSlope_translation, one_mul, mul_one]
  · simp only [affShift_mul, affShift_translation, affSlope_translation, one_mul]
    field_simp [affSlope_ne_zero g]
    ring

private theorem translationDifference_intertwines (k : AffineGroupQ → ℂ)
    (g : AffineGroupQ) (b : ℚ) :
    (translationColumnDifference k b).comp (kernelColumnRepresentation k g) =
      (kernelColumnRepresentation k g).comp
        (translationColumnDifference k (b / affSlope g)) := by
  have he : kernelColumnRepresentation k (translation b) * kernelColumnRepresentation k g =
      kernelColumnRepresentation k g *
        kernelColumnRepresentation k (translation (b / affSlope g)) := by
    rw [← map_mul, ← map_mul, translation_mul_affine]
  apply LinearMap.ext
  intro x
  change kernelColumnRepresentation k (translation b) (kernelColumnRepresentation k g x) +
      (-1 : ℂ) • kernelColumnRepresentation k g x =
    kernelColumnRepresentation k g
      (kernelColumnRepresentation k (translation (b / affSlope g)) x + (-1 : ℂ) • x)
  rw [map_add, map_smul]
  exact congrArg (fun y => y + (-1 : ℂ) • kernelColumnRepresentation k g x)
    (LinearMap.congr_fun he x)

/-- Conjugation transfers the same translation nilpotence exponent to every affine period defect. -/
theorem affinePeriodSpace_unipotent {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) (b : ℚ)
    (v : kernelColumnSpan k) (hv : v ∈ affinePeriodSpace k) :
    (translationColumnDifference k b ^ r) v = 0 := by
  have hker : affinePeriodSpace k ≤ LinearMap.ker (translationColumnDifference k b ^ r) := by
    apply Submodule.span_le.mpr
    rintro x ⟨g, rfl⟩
    have hp := Module.End.commute_pow_left_of_commute
      (translationDifference_intertwines k g b) r
    have he := LinearMap.congr_fun hp (translationPeriodDefect k 0)
    change (translationColumnDifference k b ^ r)
        (kernelColumnRepresentation k g (translationPeriodDefect k 0)) =
      kernelColumnRepresentation k g
        ((translationColumnDifference k (b / affSlope g) ^ r) (translationPeriodDefect k 0)) at he
    rw [translationPeriodSpace_unipotent hk hi hper (b / affSlope g)
      (translationPeriodDefect k 0) (Submodule.subset_span ⟨0, rfl⟩), map_zero] at he
    exact he
  exact hker hv

private theorem column_translation_pow (k : AffineGroupQ → ℂ) (b : ℚ) (n : ℕ) :
    kernelColumnRepresentation k (translation b) ^ n =
      kernelColumnRepresentation k (translation ((n : ℚ) * b)) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, translation_zero, map_one]
  | succ n ih =>
      rw [pow_succ, ih, ← map_mul, ← translation_add]
      congr 2
      push_cast
      ring

/-- A fixed integer period becomes every rational period on the unipotent defect space. -/
theorem affinePeriodSpace_fixed_of_integer_fixed {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b))
    (y : kernelColumnSpan k) (hy : y ∈ affinePeriodSpace k)
    (h1 : kernelColumnRepresentation k (translation 1) y = y) :
    ∀ b : ℚ, kernelColumnRepresentation k (translation b) y = y := by
  let H : AddSubgroup ℚ :=
    { carrier := {b | kernelColumnRepresentation k (translation b) y = y}
      zero_mem' := by simp only [translation_zero, map_one, Module.End.one_apply, Set.mem_setOf_eq]
      add_mem' := by
        intro a b ha hb
        change kernelColumnRepresentation k (translation (a + b)) y = y
        rw [translation_add, map_mul, Module.End.mul_apply, hb, ha]
      neg_mem' := by
        intro a ha
        change kernelColumnRepresentation k (translation (-a)) y = y
        calc
          kernelColumnRepresentation k (translation (-a)) y =
              kernelColumnRepresentation k (translation (-a))
                (kernelColumnRepresentation k (translation a) y) := congrArg _ ha.symm
          _ = y := by
            rw [← Module.End.mul_apply, ← map_mul, ← translation_add, neg_add_cancel,
              translation_zero, map_one, Module.End.one_apply] }
  have hz (m : ℤ) : kernelColumnRepresentation k (translation (m : ℚ)) y = y := by
    have he := H.zsmul_mem h1 m
    change kernelColumnRepresentation k (translation (m • (1 : ℚ))) y = y at he
    simpa only [zsmul_eq_mul, mul_one] using he
  intro b
  have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt b.den_pos)
  have hden : (b.den : ℚ) * b = (b.num : ℚ) := by
    calc
      (b.den : ℚ) * b = (b.den : ℚ) * ((b.num : ℚ) / (b.den : ℚ)) :=
        congrArg (fun x : ℚ => (b.den : ℚ) * x) (Rat.num_div_den b).symm
      _ = (b.num : ℚ) := by field_simp [hd]
  apply fixed_of_periodic_unipotent (kernelColumnRepresentation k (translation b)) y
    (n := r) (m := b.den) (Nat.ne_of_gt b.den_pos)
  · rw [column_translation_pow, hden]
    exact hz b.num
  · exact affinePeriodSpace_unipotent hk hi hper b y hy

/-- Every affine period defect is orthogonal to every translation-fixed column vector. -/
theorem affinePeriodSpace_orthogonal_fixed {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    (y : kernelColumnSpan k) (hy : ∀ b, kernelColumnRepresentation k (translation b) y = y)
    (x : kernelColumnSpan k) (hx : x ∈ affinePeriodSpace k) : kernelColumnPairing k x y = 0 := by
  have hδ : translationPeriodDefect k 0 = kernelColumnPoint k (translation 1) +
      (-1 : ℂ) • kernelColumnPoint k 1 := by
    apply Subtype.ext
    funext g
    change k (g⁻¹ * translation (0 + 1)) - k (g⁻¹ * translation 0) =
      k (g⁻¹ * translation 1) + (-1 : ℂ) * k (g⁻¹ * 1)
    rw [zero_add, translation_zero]
    ring
  have hbase (g : AffineGroupQ) :
      kernelColumnPairing k
        (kernelColumnRepresentation k g (translationPeriodDefect k 0)) y = 0 := by
    have hg : translation (affSlope g) * g = g * translation 1 := by
      simpa only [div_self (affSlope_ne_zero g)] using translation_mul_affine g (affSlope g)
    have he := kernelColumnPairing_invariant hk (translation (affSlope g)) (kernelColumnPoint k g) y
    rw [hy, kernelColumnRepresentation_point, hg] at he
    rw [hδ, map_add, map_smul, kernelColumnRepresentation_point, kernelColumnRepresentation_point,
      mul_one, kernelColumnPairing_add_left hk, kernelColumnPairing_smul_left hk, he]
    simp only [map_neg, map_one, neg_one_mul, add_neg_cancel]
  have hker : affinePeriodSpace k ≤ LinearMap.ker (kernelColumnPairing k y) := by
    apply Submodule.span_le.mpr
    rintro z ⟨g, rfl⟩
    change kernelColumnPairing k y
      (kernelColumnRepresentation k g (translationPeriodDefect k 0)) = 0
    rw [kernelColumnPairing_conj_symm hk, hbase, map_zero]
  rw [kernelColumnPairing_conj_symm hk,
    show kernelColumnPairing k y x = 0 from hker hx, map_zero]

/-- Finite negative index forces the entire affine period-defect space to have dimension at most `r²`. -/
theorem finite_affinePeriodSpace {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) :
    Module.Finite ℂ (affinePeriodSpace k) ∧ Module.finrank ℂ (affinePeriodSpace k) ≤ r * r := by
  let S := affinePeriodSpace k
  let P := translationColumnDifference k 1
  have hS : Set.MapsTo P S S := by
    intro x hx
    exact S.add_mem (affinePeriodSpace_invariant k (translation 1) hx) (S.smul_mem (-1 : ℂ) hx)
  let N := P.restrict hS
  have hn : N ^ r = 0 := by
    change (P.restrict hS) ^ r = 0
    rw [Module.End.pow_restrict]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact affinePeriodSpace_unipotent hk hi hper 1 x x.property
  let W := S ⊓ LinearMap.ker P
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  have hnull : ∀ x ∈ W, ∀ y ∈ W, kernelColumnPairing k x y = 0 := by
    intro x hx y hy
    have h1 : kernelColumnRepresentation k (translation 1) y = y := by
      apply Subtype.ext
      funext g
      have he := congrArg (fun z : kernelColumnSpan k => (z : AffineGroupQ → ℂ) g) hy.2
      change ((kernelColumnRepresentation k (translation 1) y : kernelColumnSpan k) :
          AffineGroupQ → ℂ) g + (-1 : ℂ) * (y : AffineGroupQ → ℂ) g = 0 at he
      change ((kernelColumnRepresentation k (translation 1) y : kernelColumnSpan k) :
        AffineGroupQ → ℂ) g = (y : AffineGroupQ → ℂ) g
      linear_combination he
    exact affinePeriodSpace_orthogonal_fixed hk y
      (affinePeriodSpace_fixed_of_integer_fixed hk hi hper y hy.1 h1) x hx.1
  obtain ⟨hfinW, hdimW⟩ := finite_isotropic_column_subspace hk hi W hnull
  letI := hfinW
  let K := LinearMap.ker N
  letI : AddCommGroup K := Module.addCommMonoidToAddCommGroup ℂ
  let L : K →ₗ[ℂ] W :=
    { toFun := fun x => ⟨(x.val : kernelColumnSpan k),
        ⟨x.val.property, congrArg Subtype.val x.property⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hinj : Function.Injective L := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : W => (z : kernelColumnSpan k)) h
  letI : Module.Finite ℂ K := Module.Finite.of_injective L hinj
  have hdimK : Module.finrank ℂ K ≤ r :=
    (LinearMap.finrank_le_finrank_of_injective hinj).trans hdimW
  obtain ⟨hfinS, hdimS⟩ := finite_of_nilpotent_finite_kernel N hn
  exact ⟨hfinS, hdimS.trans (Nat.mul_le_mul_left r hdimK)⟩

/-- Integer Haar successors have a finite affine orbit of period defects. -/
theorem finite_affinePeriodSpace_of_integerSuccessor {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k) :
    Module.Finite ℂ (affinePeriodSpace k) ∧ Module.finrank ℂ (affinePeriodSpace k) ≤ r * r :=
  finite_affinePeriodSpace hk hi (hasIntegerSuccessor_translation_periodic hs)

#print axioms translationPeriodSpace_isotropic
#print axioms finite_translationPeriodSpace
#print axioms translationPeriodSpace_unipotent
#print axioms affinePeriodSpace_unipotent
#print axioms affinePeriodSpace_fixed_of_integer_fixed
#print axioms finite_affinePeriodSpace
#print axioms finite_affinePeriodSpace_of_integerSuccessor
end GaloisForLFunctions.AdelicKreinGeometry
