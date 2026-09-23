import GaloisForLFunctions.RHTower.RealSphericalComplementarySeries

/-!
# Complementary-series generator energies

For the explicit positive complementary-series form, this file computes the exact real energy of
one raising or lowering step from a spherical `K`-type, then derives the all-vector raising
identity from infinitesimal invariance and the Casimir scalar. These closed identities are the local
input for an analytic-vector estimate: repeated derived actions shift `K`-type support by one at
a time, while the recurrence controls each shifted coefficient.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exact complementary-form energy of one raising step from `K`-type `m`. -/
theorem sphericalPrincipalE_single_complementary_energy (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    (sphericalComplementaryHermitianForm s
      (sphericalPrincipalE (s : ℂ) (Finsupp.single m 1))
      (sphericalPrincipalE (s : ℂ) (Finsupp.single m 1))).re =
        ((((2 : ℤ) * m + 1 : ℤ) : ℝ)^(2 : ℕ) - s^(2 : ℕ)) / 4 * complementaryKTypeWeight s m := by
  rw [sphericalPrincipalE_single]
  unfold sphericalComplementaryHermitianForm
  rw [diagonalKTypeHermitianForm_single]
  simp only [if_pos, mul_one]
  have hrec := complementaryKTypeWeight_succ_recurrence s hs m
  norm_num [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.mul_im,
    Complex.div_im, Complex.sub_im] at ⊢
  push_cast at hrec
  linear_combination ((2 * (m : ℝ) + 1 - s) / 4) * hrec

/-- Exact complementary-form energy of one lowering step from `K`-type `m`. -/
theorem sphericalPrincipalF_single_complementary_energy (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    (sphericalComplementaryHermitianForm s
      (sphericalPrincipalF (s : ℂ) (Finsupp.single m 1))
      (sphericalPrincipalF (s : ℂ) (Finsupp.single m 1))).re =
        ((((2 : ℤ) * m - 1 : ℤ) : ℝ)^(2 : ℕ) - s^(2 : ℕ)) / 4 * complementaryKTypeWeight s m := by
  rw [sphericalPrincipalF_single]
  unfold sphericalComplementaryHermitianForm
  rw [diagonalKTypeHermitianForm_single]
  simp only [if_pos, mul_one]
  have hrec := complementaryKTypeWeight_succ_recurrence s hs (m - 1)
  have hrec' : (2 * (m : ℝ) - 1 - s) * complementaryKTypeWeight s m =
      (2 * (m : ℝ) - 1 + s) * complementaryKTypeWeight s (m - 1) := by
    norm_num at hrec
    convert hrec using 1 <;> ring_nf
  norm_num [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.mul_im,
    Complex.div_im, Complex.sub_im] at ⊢
  linear_combination -((2 * (m : ℝ) - 1 + s) / 4) * hrec'

/-- On every finite vector, raising energy is the complementary Casimir energy.  This avoids a
coordinatewise support expansion: the exact `K`-type growth is carried by `(H + 1)²`. -/
theorem sphericalPrincipalE_complementary_energy_eq_casimir (s : ℝ) (hs : |s| < 1)
    (v : SphericalKFiniteModel) :
    sphericalComplementaryHermitianForm s
      (sphericalPrincipalE (s : ℂ) v) (sphericalPrincipalE (s : ℂ) v) =
      (1 / 4 : ℂ) * sphericalComplementaryHermitianForm s v
        (((sphericalPrincipalH + LinearMap.id).comp
          (sphericalPrincipalH + LinearMap.id)) v) -
        ((s ^ (2 : ℕ) / 4 : ℝ) : ℂ) * sphericalComplementaryHermitianForm s v v := by
  have hinv := sphericalComplementaryHermitianForm_invariant s hs v
    (sphericalPrincipalE (s : ℂ) v)
  have hcas := LinearMap.congr_fun (sphericalPrincipalCasimir_eq_smul_id (s : ℂ)) v
  have hfe : sphericalPrincipalF (s : ℂ) (sphericalPrincipalE (s : ℂ) v) =
      ((s ^ (2 : ℕ) / 4 : ℝ) : ℂ) • v - (1 / 4 : ℂ) •
        ((sphericalPrincipalH + LinearMap.id).comp
          (sphericalPrincipalH + LinearMap.id)) v := by
    dsimp [sphericalPrincipalCasimir] at hcas
    norm_num at hcas ⊢
    exact eq_sub_iff_add_eq.mpr hcas
  rw [hfe] at hinv
  simp only [map_sub, LinearMap.map_smul, smul_eq_mul] at hinv
  convert hinv using 1
  all_goals push_cast
  all_goals ring


/-- The shifted compact generator is diagonal in every spherical `K`-coordinate. -/
theorem sphericalPrincipalH_add_id_apply (v : SphericalKFiniteModel) (m : ℤ) :
    ((sphericalPrincipalH +
      (LinearMap.id : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel)) v) m =
      (((2 : ℤ) * m + 1 : ℤ) : ℂ) * v m := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [hv, hw]
      ring
  | single k z =>
      by_cases h : k = m
      · subst m
        simp [sphericalPrincipalH_single]
        ring
      · simp [sphericalPrincipalH_single, h]

/-- The squared shifted compact generator multiplies `K`-type `m` by `(2m + 1)²`. -/
theorem sphericalPrincipalH_add_id_sq_apply (v : SphericalKFiniteModel) (m : ℤ) :
    (((sphericalPrincipalH +
      (LinearMap.id : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel)).comp
      (sphericalPrincipalH + LinearMap.id)) v) m =
      ((((2 : ℤ) * m + 1 : ℤ) : ℂ) ^ (2 : ℕ)) * v m := by
  rw [LinearMap.comp_apply, sphericalPrincipalH_add_id_apply,
    sphericalPrincipalH_add_id_apply]
  ring


/-- The complementary pairing with `(H + 1)²` is the exact positive weighted `K`-type sum. -/
theorem sphericalPrincipalH_add_id_sq_complementary_pairing_re (s : ℝ)
    (v : SphericalKFiniteModel) :
    (sphericalComplementaryHermitianForm s v
      (((sphericalPrincipalH +
        (LinearMap.id : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel)).comp
        (sphericalPrincipalH + LinearMap.id)) v)).re =
      ∑ m ∈ v.support,
        ((((2 : ℤ) * m + 1 : ℤ) : ℝ) ^ (2 : ℕ)) * Complex.normSq (v m) *
          complementaryKTypeWeight s m := by
  rw [sphericalComplementaryHermitianForm, diagonalKTypeHermitianForm_apply]
  simp only [Finsupp.sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sphericalPrincipalH_add_id_sq_apply]
  let a : ℝ := (((2 : ℤ) * m + 1 : ℤ) : ℝ)
  have ha : (a : ℂ) = (((2 : ℤ) * m + 1 : ℤ) : ℂ) := by
    norm_num [a]
  have hnorm : star (v m) * v m = (Complex.normSq (v m) : ℂ) := by
    change (starRingEnd ℂ) (v m) * v m = _
    rw [← Complex.normSq_eq_conj_mul_self]
  calc
    (star (v m) * (complementaryKTypeWeight s m : ℂ) *
        ((((2 : ℤ) * m + 1 : ℤ) : ℂ) ^ (2 : ℕ) * v m)).re =
      ((complementaryKTypeWeight s m : ℂ) * (a : ℂ) ^ (2 : ℕ) *
          (star (v m) * v m)).re := by
          rw [ha]
          ring_nf
    _ = ((complementaryKTypeWeight s m : ℂ) * ((a ^ (2 : ℕ) : ℝ) : ℂ) *
          (star (v m) * v m)).re := by
          push_cast
          rfl
    _ = ((complementaryKTypeWeight s m : ℂ) * ((a ^ (2 : ℕ) : ℝ) : ℂ) *
          (Complex.normSq (v m) : ℂ)).re := by rw [hnorm]
    _ = (((a ^ (2 : ℕ) * Complex.normSq (v m) * complementaryKTypeWeight s m : ℝ) : ℂ)).re := by
          push_cast
          ring_nf
    _ = _ := by dsimp [a]

/-- A `K`-support radius bounds the squared shifted compact-generator energy. -/
theorem sphericalPrincipalH_add_id_sq_complementary_pairing_re_le_of_support (s r : ℝ) (hs : |s| < 1) (hr : 0 ≤ r)
    (v : SphericalKFiniteModel)
    (hsupp : ∀ m ∈ v.support, |(m : ℝ)| ≤ r) :
    (sphericalComplementaryHermitianForm s v
      (((sphericalPrincipalH +
        (LinearMap.id : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel)).comp
        (sphericalPrincipalH + LinearMap.id)) v)).re ≤
      (2 * r + 1) ^ (2 : ℕ) * (sphericalComplementaryHermitianForm s v v).re := by
  rw [sphericalPrincipalH_add_id_sq_complementary_pairing_re]
  change _ ≤ (2 * r + 1) ^ (2 : ℕ) *
    (diagonalKTypeHermitianForm (complementaryKTypeWeight s) v v).re
  rw [diagonalKTypeHermitianForm_self_re]
  calc
    ∑ m ∈ v.support,
        ((((2 : ℤ) * m + 1 : ℤ) : ℝ) ^ (2 : ℕ)) * Complex.normSq (v m) *
          complementaryKTypeWeight s m ≤
      ∑ m ∈ v.support,
        (2 * r + 1) ^ (2 : ℕ) * (Complex.normSq (v m) * complementaryKTypeWeight s m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hcoeff : ((((2 : ℤ) * m + 1 : ℤ) : ℝ) ^ (2 : ℕ)) ≤ (2 * r + 1) ^ (2 : ℕ) := by
        apply (sq_le_sq).2
        push_cast
        have hright : 0 ≤ 2 * r + 1 := by linarith
        rw [abs_of_nonneg hright]
        calc
          |2 * (m : ℝ) + 1| ≤ |2 * (m : ℝ)| + |1| := abs_add_le _ _
          _ = 2 * |(m : ℝ)| + 1 := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
          _ ≤ 2 * r + 1 := by linarith [hsupp m hm]
      calc
        ((((2 : ℤ) * m + 1 : ℤ) : ℝ) ^ (2 : ℕ)) * Complex.normSq (v m) *
            complementaryKTypeWeight s m ≤
          ((2 * r + 1) ^ (2 : ℕ) * Complex.normSq (v m)) *
            complementaryKTypeWeight s m := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoeff (Complex.normSq_nonneg _))
                (le_of_lt (complementaryKTypeWeight_pos s hs m))
        _ = (2 * r + 1) ^ (2 : ℕ) *
            (Complex.normSq (v m) * complementaryKTypeWeight s m) := by ring
    _ = (2 * r + 1) ^ (2 : ℕ) * ∑ m ∈ v.support,
        Complex.normSq (v m) * complementaryKTypeWeight s m := by
      rw [Finset.mul_sum]
/-- Raising shifts finite `K`-coordinates by one with its exact principal coefficient. -/
theorem sphericalPrincipalE_apply (s : ℂ) (v : SphericalKFiniteModel) (m : ℤ) :
    sphericalPrincipalE s v m =
      ((s - 1 - 2 * ((m - 1 : ℤ) : ℂ)) / 2) * v (m - 1) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [hv, hw]
      ring
  | single k z =>
      by_cases h : k + 1 = m
      · subst m
        simp [sphericalPrincipalE_single]
      · have hback : k ≠ m - 1 := by omega
        simp [sphericalPrincipalE_single, h, hback]

/-- Lowering shifts finite `K`-coordinates by one with its exact principal coefficient. -/
theorem sphericalPrincipalF_apply (s : ℂ) (v : SphericalKFiniteModel) (m : ℤ) :
    sphericalPrincipalF s v m =
      ((s - 1 + 2 * ((m + 1 : ℤ) : ℂ)) / 2) * v (m + 1) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [hv, hw]
      ring
  | single k z =>
      by_cases h : k - 1 = m
      · subst m
        simp [sphericalPrincipalF_single]
      · have hback : k ≠ m + 1 := by omega
        simp [sphericalPrincipalF_single, h, hback]
/-- Raising increases the real `K`-support radius by at most one. -/
theorem sphericalPrincipalE_support_radius (s : ℂ) (v : SphericalKFiniteModel) (r : ℝ)
    (hsupp : ∀ m ∈ v.support, |(m : ℝ)| ≤ r) :
    ∀ m ∈ (sphericalPrincipalE s v).support, |(m : ℝ)| ≤ r + 1 := by
  intro m hm
  have hnonzero : sphericalPrincipalE s v m ≠ 0 := Finsupp.mem_support_iff.mp hm
  rw [sphericalPrincipalE_apply] at hnonzero
  have hv : v (m - 1) ≠ 0 := by
    intro hz
    exact hnonzero (by rw [hz, mul_zero])
  have hbase := hsupp (m - 1) (Finsupp.mem_support_iff.mpr hv)
  calc
    |(m : ℝ)| = |((m - 1 : ℤ) : ℝ) + 1| := by
      congr 1
      push_cast
      ring
    _ ≤ |((m - 1 : ℤ) : ℝ)| + |1| := abs_add_le _ _
    _ = |((m - 1 : ℤ) : ℝ)| + 1 := by norm_num
    _ ≤ r + 1 := by linarith

/-- Lowering increases the real `K`-support radius by at most one. -/
theorem sphericalPrincipalF_support_radius (s : ℂ) (v : SphericalKFiniteModel) (r : ℝ)
    (hsupp : ∀ m ∈ v.support, |(m : ℝ)| ≤ r) :
    ∀ m ∈ (sphericalPrincipalF s v).support, |(m : ℝ)| ≤ r + 1 := by
  intro m hm
  have hnonzero : sphericalPrincipalF s v m ≠ 0 := Finsupp.mem_support_iff.mp hm
  rw [sphericalPrincipalF_apply] at hnonzero
  have hv : v (m + 1) ≠ 0 := by
    intro hz
    exact hnonzero (by rw [hz, mul_zero])
  have hbase := hsupp (m + 1) (Finsupp.mem_support_iff.mpr hv)
  calc
    |(m : ℝ)| = |((m + 1 : ℤ) : ℝ) - 1| := by
      congr 1
      push_cast
      ring
    _ ≤ |((m + 1 : ℤ) : ℝ)| + |(-1)| := by
      rw [sub_eq_add_neg]
      exact abs_add_le _ _
    _ = |((m + 1 : ℤ) : ℝ)| + 1 := by norm_num
    _ ≤ r + 1 := by linarith

/-- A finite `K`-support radius controls the complementary energy after raising. -/
theorem sphericalPrincipalE_complementary_energy_re_le_of_support (s r : ℝ) (hs : |s| < 1)
    (hr : 0 ≤ r) (v : SphericalKFiniteModel)
    (hsupp : ∀ m ∈ v.support, |(m : ℝ)| ≤ r) :
    (sphericalComplementaryHermitianForm s
      (sphericalPrincipalE (s : ℂ) v) (sphericalPrincipalE (s : ℂ) v)).re ≤
      ((2 * r + 1) ^ (2 : ℕ) / 4) * (sphericalComplementaryHermitianForm s v v).re := by
  have hcas' :
      (sphericalComplementaryHermitianForm s
        (sphericalPrincipalE (s : ℂ) v) (sphericalPrincipalE (s : ℂ) v)).re =
        (1 / 4 : ℝ) * (sphericalComplementaryHermitianForm s v
          (((sphericalPrincipalH + LinearMap.id).comp
            (sphericalPrincipalH + LinearMap.id)) v)).re -
          (s ^ (2 : ℕ) / 4) * (sphericalComplementaryHermitianForm s v v).re := by
    rw [sphericalPrincipalE_complementary_energy_eq_casimir s hs v]
    have hsquare_re : ((s : ℂ) ^ (2 : ℕ)).re = s ^ (2 : ℕ) := by
      rw [show (s : ℂ) ^ (2 : ℕ) = (s : ℂ) * s by ring, Complex.mul_re]
      norm_num
      ring
    have hsquare_im : ((s : ℂ) ^ (2 : ℕ)).im = 0 := by
      rw [show (s : ℂ) ^ (2 : ℕ) = (s : ℂ) * s by ring, Complex.mul_im]
      norm_num
    rw [Complex.sub_re, Complex.mul_re, Complex.mul_re]
    norm_num [Complex.ofReal_re, Complex.ofReal_im]
    rw [hsquare_re, hsquare_im]
    ring
  have hK := sphericalPrincipalH_add_id_sq_complementary_pairing_re_le_of_support s r hs hr v hsupp
  have hB : 0 ≤ (sphericalComplementaryHermitianForm s v v).re := by
    rw [sphericalComplementaryHermitianForm, diagonalKTypeHermitianForm_self_re]
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (Complex.normSq_nonneg _)
      (le_of_lt (complementaryKTypeWeight_pos s hs m))
  rw [hcas']
  nlinarith [sq_nonneg s]

/-- Reflection of the finite `K`-type coordinate. -/
def sphericalKReflection : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  Finsupp.lmapDomain ℂ ℂ (fun m : ℤ => -m)

/-- Reflection sends the `m`th `K`-type basis vector to the `-m`th one. -/
theorem sphericalKReflection_single (m : ℤ) (z : ℂ) :
    sphericalKReflection (Finsupp.single m z) = Finsupp.single (-m) z := by
  simp [sphericalKReflection, Finsupp.lmapDomain_apply]

/-- Reflection reads the finite coordinate at its negative index. -/
theorem sphericalKReflection_apply (v : SphericalKFiniteModel) (m : ℤ) :
    sphericalKReflection v m = v (-m) := by
  change (Finsupp.mapDomain (fun n : ℤ => -n) v) m = v (-m)
  simpa using Finsupp.mapDomain_apply (f := fun n : ℤ => -n)
    (by intro a b h; exact neg_injective h) v (-m)

/-- Reflection exchanges raising with lowering. -/
theorem sphericalKReflection_E (s : ℂ) :
    sphericalKReflection.comp (sphericalPrincipalE s) =
      (sphericalPrincipalF s).comp sphericalKReflection := by
  apply Finsupp.lhom_ext
  intro m z
  rw [show Finsupp.single m z = z • Finsupp.single m 1 by simp, map_smul, map_smul]
  congr 1
  simp only [LinearMap.comp_apply, sphericalKReflection_single,
    sphericalPrincipalE_single, sphericalPrincipalF_single]
  push_cast
  ring

/-- Reflection exchanges lowering with raising. -/
theorem sphericalKReflection_F (s : ℂ) :
    sphericalKReflection.comp (sphericalPrincipalF s) =
      (sphericalPrincipalE s).comp sphericalKReflection := by
  apply Finsupp.lhom_ext
  intro m z
  rw [show Finsupp.single m z = z • Finsupp.single m 1 by simp, map_smul, map_smul]
  congr 1
  simp only [LinearMap.comp_apply, sphericalKReflection_single,
    sphericalPrincipalE_single, sphericalPrincipalF_single]
  push_cast
  ring

/-- Reflection preserves every diagonal Hermitian form whose real weights are even. -/
theorem sphericalKReflection_diagonal_form (q : ℤ → ℝ)
    (hq : ∀ m, q (-m) = q m) (v w : SphericalKFiniteModel) :
    diagonalKTypeHermitianForm q (sphericalKReflection v) (sphericalKReflection w) =
      diagonalKTypeHermitianForm q v w := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ hv₁ hv₂ =>
      simp only [map_add, LinearMap.add_apply]
      rw [hv₁, hv₂]
  | single m z =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ =>
          simp only [map_add]
          rw [hw₁, hw₂]
      | single n w =>
          rw [sphericalKReflection_single, sphericalKReflection_single,
            diagonalKTypeHermitianForm_single, diagonalKTypeHermitianForm_single]
          by_cases h : m = n
          · subst n
            simp [hq]
          · simp [h]

/-- The complementary-series Hermitian form is invariant under `K`-type reflection. -/
theorem sphericalKReflection_complementary_form (s : ℝ)
    (v w : SphericalKFiniteModel) :
    sphericalComplementaryHermitianForm s (sphericalKReflection v) (sphericalKReflection w) =
      sphericalComplementaryHermitianForm s v w := by
  exact sphericalKReflection_diagonal_form (complementaryKTypeWeight s)
    (by intro m; simp [complementaryKTypeWeight]) v w

/-- Finite `K`-type reflection is an involution. -/
theorem sphericalKReflection_sq :
    sphericalKReflection.comp sphericalKReflection = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  simp [sphericalKReflection_single]

/-- A finite `K`-support radius controls the complementary energy after lowering. -/
theorem sphericalPrincipalF_complementary_energy_re_le_of_support (s r : ℝ)
    (hs : |s| < 1) (hr : 0 ≤ r) (v : SphericalKFiniteModel)
    (hsupp : ∀ m ∈ v.support, |(m : ℝ)| ≤ r) :
    (sphericalComplementaryHermitianForm s
      (sphericalPrincipalF (s : ℂ) v) (sphericalPrincipalF (s : ℂ) v)).re ≤
      ((2 * r + 1) ^ (2 : ℕ) / 4) * (sphericalComplementaryHermitianForm s v v).re := by
  have hRsupp : ∀ m ∈ (sphericalKReflection v).support, |(m : ℝ)| ≤ r := by
    intro m hm
    have hnonzero : sphericalKReflection v m ≠ 0 := Finsupp.mem_support_iff.mp hm
    rw [sphericalKReflection_apply] at hnonzero
    have hbase := hsupp (-m) (Finsupp.mem_support_iff.mpr hnonzero)
    simpa using hbase
  have hE := sphericalPrincipalE_complementary_energy_re_le_of_support s r hs hr
    (sphericalKReflection v) hRsupp
  have hR2 := LinearMap.congr_fun sphericalKReflection_sq v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hR2
  have hinter := LinearMap.congr_fun (sphericalKReflection_E (s : ℂ))
    (sphericalKReflection v)
  simp only [LinearMap.comp_apply] at hinter
  have hF : sphericalPrincipalF (s : ℂ) v =
      sphericalKReflection (sphericalPrincipalE (s : ℂ) (sphericalKReflection v)) := by
    calc
      sphericalPrincipalF (s : ℂ) v =
          sphericalPrincipalF (s : ℂ) (sphericalKReflection (sphericalKReflection v)) := by
            rw [hR2]
      _ = sphericalKReflection
          (sphericalPrincipalE (s : ℂ) (sphericalKReflection v)) := hinter.symm
  calc
    (sphericalComplementaryHermitianForm s
        (sphericalPrincipalF (s : ℂ) v) (sphericalPrincipalF (s : ℂ) v)).re =
      (sphericalComplementaryHermitianForm s
        (sphericalPrincipalE (s : ℂ) (sphericalKReflection v))
        (sphericalPrincipalE (s : ℂ) (sphericalKReflection v))).re := by
          rw [hF, sphericalKReflection_complementary_form]
    _ ≤ ((2 * r + 1) ^ (2 : ℕ) / 4) *
        (sphericalComplementaryHermitianForm s
          (sphericalKReflection v) (sphericalKReflection v)).re := hE
    _ = ((2 * r + 1) ^ (2 : ℕ) / 4) * (sphericalComplementaryHermitianForm s v v).re := by
      rw [sphericalKReflection_complementary_form]
end

end GaloisForLFunctions.RHTower
