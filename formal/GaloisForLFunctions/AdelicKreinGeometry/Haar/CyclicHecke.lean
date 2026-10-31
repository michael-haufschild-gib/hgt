import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicOrbits
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationMovingPositivity
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnPositivity

/-!
# Finite cyclic Hecke bounds

Cyclic Haar orbits control pairings of moving dilation columns. Cauchy–Schwarz
on the nonnegative translation-difference space bounds their squared modulus by
the reciprocal reduced denominator of the dilation ratio.
-/

open Complex Module Finset
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The moving component of a dilation column under one cyclic translation projection. -/
def movingDilationColumn (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) : kernelColumnSpan k :=
  kernelColumnPoint k (dilation a) + (-1 : ℂ) •
    translationFixedProjection k hp b (kernelColumnPoint k (dilation a))

theorem movingDilationColumn_eq_sub (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    movingDilationColumn k hp b a = kernelColumnPoint k (dilation a) -
      translationFixedProjection k hp b (kernelColumnPoint k (dilation a)) := by
  apply Subtype.ext
  funext g
  change (kernelColumnPoint k (dilation a) : AffineGroupQ → ℂ) g + (-1 : ℂ) *
    (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)) : AffineGroupQ → ℂ) g =
      (kernelColumnPoint k (dilation a) : AffineGroupQ → ℂ) g -
        (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)) : AffineGroupQ → ℂ) g
  ring

theorem movingDilationColumn_mem_range (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    movingDilationColumn k hp b a ∈
      LinearMap.range (kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1) :=
  add_neg_locallyPeriodicProjection_mem_range _ (kernel_translation_locally_periodic hp b) _

theorem movingDilationColumn_nonneg {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    0 ≤ (kernelColumnPairing k (movingDilationColumn k hp b a)
      (movingDilationColumn k hp b a)).re :=
  translation_moving_subspace_nonnegative hk hi hp b _
    (movingDilationColumn_mem_range k hp b a)

/-- Removing the cyclic fixed component leaves a dilation-column norm at most one. -/
theorem movingDilationColumn_pairing_le_one {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    (kernelColumnPairing k (movingDilationColumn k hp b a)
      (movingDilationColumn k hp b a)).re ≤ 1 := by
  let v := kernelColumnPoint k (dilation a)
  have hv : kernelColumnPairing k v v = 1 := by
    rw [kernelColumnPairing_point_left hk]
    change k ((dilation a)⁻¹ * dilation a) = 1
    rw [inv_mul_cancel, hasIntegerSuccessor_one hs]
  have hsplit : kernelColumnPairing k v v =
      kernelColumnPairing k (translationFixedProjection k hp b v)
        (translationFixedProjection k hp b v) +
      kernelColumnPairing k (movingDilationColumn k hp b a)
        (movingDilationColumn k hp b a) := by
    simpa only [movingDilationColumn_eq_sub, translationFixedProjection] using
      kernelColumnPairing_projection_decomposition hk (translation b)
        (kernel_translation_locally_periodic hp b) v v
  rw [hv] at hsplit
  have he := congrArg Complex.re hsplit
  rw [Complex.one_re, Complex.add_re] at he
  have hnonneg := integer_successor_projection_pairing_nonneg hk hs hp b a
  linarith only [he, hnonneg]

/-- A cyclic fixed projection is fixed by every natural multiple of its step. -/
theorem translationFixedProjection_fixed_nat_multiple (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (n : ℕ) (x : kernelColumnSpan k) :
    kernelColumnRepresentation k (translation ((n : ℚ) * b))
      (translationFixedProjection k hp b x) = translationFixedProjection k hp b x := by
  rw [← rational_affine_translation_pow]
  have hfix : kernelColumnRepresentation k (translation b)
      (translationFixedProjection k hp b x) = translationFixedProjection k hp b x :=
    locallyPeriodicProjection_fixed _ (kernel_translation_locally_periodic hp b) x
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]

/-- A dilation column and its moving part retain the translation period given by their slope. -/
theorem movingDilationColumn_fixed (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (c : ℚˣ)
    {n : ℕ} (hc : (c : ℚ) = (n : ℚ) * b) :
    kernelColumnRepresentation k (translation (c : ℚ)) (movingDilationColumn k hp b c) =
      movingDilationColumn k hp b c := by
  have hv := kernel_translation_column_period hp (c : ℚ) (dilation c)
  rw [affSlope_dilation, div_self c.ne_zero, Rat.den_one, pow_one] at hv
  have hproj : kernelColumnRepresentation k (translation (c : ℚ))
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation c))) =
      translationFixedProjection k hp b (kernelColumnPoint k (dilation c)) := by
    rw [hc]
    exact translationFixedProjection_fixed_nat_multiple k hp b n _
  simp only [movingDilationColumn, map_add, map_smul, hv, hproj]

/-- Cyclic translates at a multiple of the projection step stay in its moving subspace. -/
theorem movingDilationColumn_orbit_mem (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a c : ℚˣ)
    {n : ℕ} (hc : (c : ℚ) = (n : ℚ) * b) (j : ℕ) :
    (((kernelColumnRepresentation k (translation (c : ℚ))) ^ j)
      (movingDilationColumn k hp b a)) ∈
      LinearMap.range (kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1) := by
  have hU : kernelColumnRepresentation k (translation (c : ℚ)) =
      (kernelColumnRepresentation k (translation b)) ^ n := by
    rw [rational_affine_translation_pow, ← hc]
  apply (locallyPeriodicProjection_apply_eq_zero_iff _
    (kernel_translation_locally_periodic hp b) _).mp
  rw [hU, ← pow_mul, locallyPeriodicProjection_pow_apply]
  exact (locallyPeriodicProjection_apply_eq_zero_iff _
    (kernel_translation_locally_periodic hp b) _).mpr (movingDilationColumn_mem_range k hp b a)

/-- Cyclic Haar orthogonality bounds the moving correlation by the reciprocal rational denominator. -/
theorem normSq_movingDilationColumn_pairing_le_inv_den {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a c : ℚˣ)
    {n : ℕ} (hc : (c : ℚ) = (n : ℚ) * b) :
    normSq (kernelColumnPairing k (movingDilationColumn k hp b a)
      (movingDilationColumn k hp b c)) ≤ 1 / ((c / (a : ℚ)).den : ℝ) := by
  classical
  let d := (c / (a : ℚ)).den
  let T := kernelColumnRepresentation k (translation (c : ℚ))
  let v := kernelColumnPoint k (dilation a)
  let p := translationFixedProjection k hp b v
  let u := movingDilationColumn k hp b a
  let w := movingDilationColumn k hp b c
  let W := LinearMap.range (kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1)
  let A := kernelColumnSynthesis (fun i : Fin d => (T ^ i.val) u) (fun _ => 1)
  let S := kernelColumnSynthesis (fun i : Fin d => (T ^ i.val) v) (fun _ => 1)
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (show 0 < d from ((c : ℚ) / (a : ℚ)).den_pos)
  have hW : ∀ x ∈ W, 0 ≤ (kernelColumnPairing k x x).re :=
    fun x hx => translation_moving_subspace_nonnegative hk hi hp b x hx
  have hAmem : A ∈ W := by
    change (∑ i : Fin d, (1 : ℂ) • (T ^ i.val) u) ∈ W
    exact W.sum_mem (fun i _ => W.smul_mem 1
      (movingDilationColumn_orbit_mem k hp b a c hc i.val))
  have hwmem : w ∈ W := movingDilationColumn_mem_range k hp b c
  have hpfix : T p = p := by
    change kernelColumnRepresentation k (translation (c : ℚ)) p = p
    rw [hc]
    exact translationFixedProjection_fixed_nat_multiple k hp b n v
  have hppow (j : ℕ) : (T ^ j) p = p := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hpfix, ih]
  have hAexpr : A = S + (-(d : ℂ)) • p := by
    change (∑ i : Fin d, (1 : ℂ) • (T ^ i.val) (v + (-1 : ℂ) • p)) =
      (∑ i : Fin d, (1 : ℂ) • (T ^ i.val) v) + (-(d : ℂ)) • p
    simp only [one_smul, map_add, map_smul, hppow, sum_add_distrib, sum_const,
      card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ d, smul_smul, mul_neg, mul_one]
  have hSsplit : S = A + (d : ℂ) • p := by
    rw [hAexpr, add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  have horth (i j : Fin d) (hij : i ≠ j) :
      kernelColumnPairing k ((T ^ i.val) v) ((T ^ j.val) v) = 0 := by
    have h := integer_successor_translation_orbit_orthonormal hk hs a (c : ℚ) i.isLt j.isLt
    rw [if_neg (fun he => hij (Fin.ext he))] at h
    exact h
  have hdiag (i : Fin d) : kernelColumnPairing k ((T ^ i.val) v) ((T ^ i.val) v) = 1 := by
    have h := integer_successor_translation_orbit_orthonormal hk hs a (c : ℚ) i.isLt i.isLt
    rw [if_pos rfl] at h
    exact h
  have hSS : kernelColumnPairing k S S = (d : ℂ) := by
    have h := kernelColumnPairing_synthesis_orthogonal hk
      (fun i : Fin d => (T ^ i.val) v) horth (fun _ => 1)
    simpa only [normSq_one, Complex.ofReal_one, one_mul, hdiag, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  have hpA : kernelColumnPairing k p A = 0 :=
    kernelColumnPairing_fixed_moving hk (translation b) p A
      (locallyPeriodicProjection_fixed _ (kernel_translation_locally_periodic hp b) v) hAmem
  have hAp : kernelColumnPairing k A p = 0 := by
    rw [kernelColumnPairing_conj_symm hk, hpA, map_zero]
  have hAnorm : (kernelColumnPairing k A A).re ≤ (d : ℝ) := by
    have he : kernelColumnPairing k S S = kernelColumnPairing k A A +
        (d : ℂ) ^ 2 * kernelColumnPairing k p p := by
      rw [hSsplit]
      simp only [kernelColumnPairing_add_left hk, kernelColumnPairing_smul_left hk,
        map_add, map_smul, smul_eq_mul, map_natCast, hpA, hAp,
        mul_zero, add_zero, zero_add]
      ring
    rw [hSS] at he
    have hre := congrArg Complex.re he
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, mul_zero, sub_zero, add_zero] at hre
    have hpnonneg : 0 ≤ (kernelColumnPairing k p p).re :=
      integer_successor_projection_pairing_nonneg hk hs hp b a
    have hm := mul_nonneg (mul_self_nonneg (d : ℝ)) hpnonneg
    linarith only [hre, hm]
  have hwfix : T w = w := movingDilationColumn_fixed k hp b c hc
  have hwpow (j : ℕ) : (T ^ j) w = w := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hwfix, ih]
  have hpair (i : Fin d) : kernelColumnPairing k ((T ^ i.val) u) w =
      kernelColumnPairing k u w := by
    have h := kernelColumnPairing_invariant hk ((translation (c : ℚ)) ^ i.val) u w
    rw [map_pow] at h
    change kernelColumnPairing k ((T ^ i.val) u) ((T ^ i.val) w) = _ at h
    rwa [hwpow] at h
  have hAw : kernelColumnPairing k A w = (d : ℂ) * kernelColumnPairing k u w := by
    rw [kernelColumnPairing_synthesis hk]
    simp only [map_one, one_mul, hpair, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hCS := kernelColumnPairing_normSq_le_on_subspace hk W hW A w hAmem hwmem
  have hwnorm : (kernelColumnPairing k w w).re ≤ 1 :=
    movingDilationColumn_pairing_le_one hk hs hp b c
  have hprod : (kernelColumnPairing k A A).re * (kernelColumnPairing k w w).re ≤
      (kernelColumnPairing k A A).re := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hwnorm (hW A hAmem)
  have hbound := hCS.trans (hprod.trans hAnorm)
  have hdnorm : normSq (d : ℂ) = (d : ℝ) ^ 2 := by
    norm_num [Complex.normSq_apply, pow_two]
  rw [hAw, normSq_mul, hdnorm] at hbound
  apply (le_div_iff₀ hd).mpr
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith only [hbound]

#print axioms movingDilationColumn_nonneg
#print axioms movingDilationColumn_pairing_le_one
#print axioms movingDilationColumn_fixed
#print axioms movingDilationColumn_orbit_mem
#print axioms normSq_movingDilationColumn_pairing_le_inv_den
end GaloisForLFunctions.AdelicKreinGeometry
