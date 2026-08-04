import GaloisForLFunctions.HTGeometry.StokesCartanLorentzCapacity

/-!
# Stokes Euler--fusion capacity law

This module globalizes the one-pole Stokes--Cartan capacity theorem.  A connected wild curve is
assembled from marked one-pole atoms by identifying their physical-rank ports.  On this rank fibre
product, quasi-Hamiltonian fusion and genus contribute only one common-rank square.  Centering each
atom therefore leaves a positive direct sum plus one scalar Euler--capacity gap

`χ(Σ) + ∑ a, (Ωₐ - 2)`.

The theorem is stated for a dependent family of finite local Stokes spaces: different punctures may
have different numbers of local vertices.  All identities and sign consequences are unconditional.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes
namespace EulerFusionCapacity

/-- Sum of the marked one-pole Cartan forms before global fusion. -/
def localCartanSum {m : ℕ} {n : Fin m → ℕ}
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) : ℝ :=
  ∑ a, (datum a).cartanQuadratic (x a)

/-- Positive energy of all locally centered Stokes modes. -/
noncomputable def centeredEnergy {m : ℕ} {n : Fin m → ℕ}
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) : ℝ :=
  ∑ a, (datum a).positiveQuadratic ((datum a).centeredVector (x a))

/-- The global marked deformation form.  The correction `2(1-g-m) M²` is the exact difference
between the genus-`g`, `m`-puncture quasi-Hamiltonian dimension formula and the sum of its `m`
one-pole specializations. -/
def fusionQuadratic {m : ℕ} {n : Fin m → ℕ} (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) (commonRank : ℝ) : ℝ :=
  localCartanSum datum x +
    2 * (1 - (genus : ℝ) - (m : ℝ)) * commonRank ^ 2

/-- Euler characteristic of the compact base curve. -/
def baseEulerCharacteristic (genus : ℕ) : ℝ := 2 - 2 * (genus : ℝ)

/-- The unique global port gap after identifying all local physical ranks. -/
noncomputable def globalCapacityGap {m : ℕ} {n : Fin m → ℕ} (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) : ℝ :=
  (∑ a, (datum a).capacityGap) - 2 * ((genus : ℝ) + (m : ℝ) - 1)

/-- Equivalent Gauss--Bonnet normalization: Euler characteristic plus one renormalized local
Stokes capacity at every puncture. -/
noncomputable def eulerCapacityGap {m : ℕ} {n : Fin m → ℕ} (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) : ℝ :=
  baseEulerCharacteristic genus + ∑ a, ((datum a).capacityGap - 2)

/-- Renormalized local capacity defect.  The constant two is forced by the one-puncture sphere. -/
noncomputable def localCapacityDefect {n : ℕ} (datum : CertifiedFissionDatum n) : ℝ :=
  2 - datum.capacityGap

/-- Gauss--Bonnet normalization of the universal scalar channel: Euler characteristic minus the
sum of local capacity defects. -/
theorem eulerCapacityGap_eq_eulerCharacteristic_sub_defects
    {m : ℕ} {n : Fin m → ℕ} (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) :
    eulerCapacityGap genus datum = baseEulerCharacteristic genus -
      ∑ a, localCapacityDefect (datum a) := by
  simp only [eulerCapacityGap, localCapacityDefect, Finset.sum_sub_distrib]
  ring

theorem globalCapacityGap_eq_eulerCapacityGap {m : ℕ} {n : Fin m → ℕ}
    (genus : ℕ) (datum : (a : Fin m) → CertifiedFissionDatum (n a)) :
    globalCapacityGap genus datum = eulerCapacityGap genus datum := by
  simp only [globalCapacityGap, eulerCapacityGap, baseEulerCharacteristic,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Adding one handle subtracts exactly two from the unique Euler--capacity channel. -/
theorem eulerCapacityGap_succ_genus {m : ℕ} {n : Fin m → ℕ}
    (genus : ℕ) (datum : (a : Fin m) → CertifiedFissionDatum (n a)) :
    eulerCapacityGap (genus + 1) datum = eulerCapacityGap genus datum - 2 := by
  simp only [eulerCapacityGap, baseEulerCharacteristic]
  push_cast
  ring

/-- The local capacity completions add exactly when all local ports carry the same rank. -/
theorem localCartanSum_eq_centered {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a)))
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) (commonRank : ℝ)
    (hmass : ∀ a, (datum a).totalRamification (x a) = commonRank) :
    localCartanSum datum x = centeredEnergy datum x +
      commonRank ^ 2 * ∑ a, (datum a).capacityGap := by
  calc
    localCartanSum datum x =
        ∑ a, ((datum a).positiveQuadratic ((datum a).centeredVector (x a)) +
          (datum a).totalRamification (x a) ^ 2 * (datum a).capacityGap) := by
      apply Finset.sum_congr rfl
      intro a _
      exact @CertifiedFissionDatum.cartanQuadratic_eq_centered_capacity
        (n a) (hNonempty a) (datum a) (x a)
    _ = ∑ a, ((datum a).positiveQuadratic ((datum a).centeredVector (x a)) +
          commonRank ^ 2 * (datum a).capacityGap) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hmass a]
    _ = centeredEnergy datum x + commonRank ^ 2 * ∑ a, (datum a).capacityGap := by
      rw [centeredEnergy, Finset.sum_add_distrib, Finset.mul_sum]

/-- **Stokes Euler--capacity law.**  Every global compatible mode is the orthogonal sum of
positive local rank-zero modes and one common physical-rank mode. -/
theorem fusionQuadratic_eq_centered_eulerCapacity {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) (commonRank : ℝ)
    (hmass : ∀ a, (datum a).totalRamification (x a) = commonRank) :
    fusionQuadratic genus datum x commonRank = centeredEnergy datum x +
      commonRank ^ 2 * eulerCapacityGap genus datum := by
  rw [fusionQuadratic, localCartanSum_eq_centered hNonempty datum x commonRank hmass,
    ← globalCapacityGap_eq_eulerCapacityGap genus datum]
  simp only [globalCapacityGap]
  ring

theorem centeredEnergy_nonneg {m : ℕ} {n : Fin m → ℕ}
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) : 0 ≤ centeredEnergy datum x := by
  rw [centeredEnergy]
  apply Finset.sum_nonneg
  intro a _
  exact (datum a).positiveQuadratic_nonneg _

theorem centeredEnergy_pos_of_exists {m : ℕ} {n : Fin m → ℕ}
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ)
    (hex : ∃ a, (datum a).centeredVector (x a) ≠ 0) :
    0 < centeredEnergy datum x := by
  obtain ⟨a, ha⟩ := hex
  rw [centeredEnergy]
  apply Finset.sum_pos'
  · intro b _
    exact (datum b).positiveQuadratic_nonneg _
  · exact ⟨a, Finset.mem_univ _, (datum a).positiveQuadratic_pos ha⟩

/-- Positive phase: the global form is positive away from the zero centered/rank coordinates. -/
theorem fusionQuadratic_pos_of_eulerCapacityGap_pos {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) (commonRank : ℝ)
    (hmass : ∀ a, (datum a).totalRamification (x a) = commonRank)
    (hgap : 0 < eulerCapacityGap genus datum)
    (hmode : (∃ a, (datum a).centeredVector (x a) ≠ 0) ∨ commonRank ≠ 0) :
    0 < fusionQuadratic genus datum x commonRank := by
  rw [fusionQuadratic_eq_centered_eulerCapacity hNonempty genus datum x commonRank hmass]
  rcases hmode with hspatial | hmassNonzero
  · exact add_pos_of_pos_of_nonneg (centeredEnergy_pos_of_exists datum x hspatial)
      (mul_nonneg (sq_nonneg _) hgap.le)
  · exact add_pos_of_nonneg_of_pos (centeredEnergy_nonneg datum x)
      (mul_pos (sq_pos_of_ne_zero hmassNonzero) hgap)

/-- Affine phase: at a zero Euler--capacity gap the global form is nonnegative. -/
theorem fusionQuadratic_nonneg_of_eulerCapacityGap_eq_zero {m : ℕ}
    {n : Fin m → ℕ} (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) (commonRank : ℝ)
    (hmass : ∀ a, (datum a).totalRamification (x a) = commonRank)
    (hgap : eulerCapacityGap genus datum = 0) :
    0 ≤ fusionQuadratic genus datum x commonRank := by
  rw [fusionQuadratic_eq_centered_eulerCapacity hNonempty genus datum x commonRank hmass,
    hgap]
  simpa using centeredEnergy_nonneg datum x

/-- The rank-zero hyperplane is strictly positive independently of genus and number of punctures. -/
theorem fusionQuadratic_pos_of_commonRank_eq_zero {m : ℕ} {n : Fin m → ℕ}
    (genus : ℕ) (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ)
    (hmass : ∀ a, (datum a).totalRamification (x a) = 0) (hx : x ≠ 0) :
    0 < fusionQuadratic genus datum x 0 := by
  have hex : ∃ a, x a ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext a i
    exact congrFun (h a) i
  simp only [fusionQuadratic, localCartanSum, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, add_zero]
  obtain ⟨a, ha⟩ := hex
  apply Finset.sum_pos'
  · intro b _
    by_cases hb : x b = 0
    · rw [hb]
      simp [CertifiedFissionDatum.cartanQuadratic, FiniteQuadratic.qform]
    · exact (CertifiedFissionDatum.cartanQuadratic_pos_of_totalRamification_eq_zero
        (datum b) (hmass b) hb).le
  · exact ⟨a, Finset.mem_univ _,
      CertifiedFissionDatum.cartanQuadratic_pos_of_totalRamification_eq_zero
        (datum a) (hmass a) ha⟩

/-- The simultaneous capacity ray is the unique global nonspatial direction. -/
noncomputable def capacityRay {m : ℕ} {n : Fin m → ℕ}
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) (commonRank : ℝ)
    (a : Fin m) : Fin (n a) → ℝ :=
  (commonRank / (datum a).capacity) • (datum a).capacityVector

theorem capacityRay_mass {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a)))
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) (commonRank : ℝ)
    (a : Fin m) :
    (datum a).totalRamification (capacityRay datum commonRank a) = commonRank := by
  letI : Nonempty (Fin (n a)) := hNonempty a
  change (datum a).massLinear (capacityRay datum commonRank a) = commonRank
  rw [capacityRay, LinearMap.map_smul, (datum a).massLinear_apply,
    (datum a).totalRamification_capacityVector]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt (datum a).capacity_pos]

theorem capacityRay_centered {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a)))
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) (commonRank : ℝ)
    (a : Fin m) :
    (datum a).centeredVector (capacityRay datum commonRank a) = 0 := by
  letI : Nonempty (Fin (n a)) := hNonempty a
  rw [CertifiedFissionDatum.centeredVector,
    capacityRay_mass hNonempty datum commonRank a]
  simp [capacityRay]

/-- Exact value of the global form on its common capacity ray. -/
theorem fusionQuadratic_capacityRay {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) (commonRank : ℝ) :
    fusionQuadratic genus datum (capacityRay datum commonRank) commonRank =
      commonRank ^ 2 * eulerCapacityGap genus datum := by
  rw [fusionQuadratic_eq_centered_eulerCapacity hNonempty genus datum
    (capacityRay datum commonRank) commonRank (capacityRay_mass hNonempty datum commonRank)]
  have henergy : centeredEnergy datum (capacityRay datum commonRank) = 0 := by
    rw [centeredEnergy]
    apply Finset.sum_eq_zero
    intro a _
    rw [capacityRay_centered hNonempty datum commonRank a]
    simp [CertifiedFissionDatum.positiveQuadratic, FiniteQuadratic.qform]
  rw [henergy, zero_add]

/-- The simultaneous capacity ray is the global constrained minimizer at fixed physical rank. -/
theorem fusionQuadratic_capacityRay_le {m : ℕ} {n : Fin m → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a))
    (x : (a : Fin m) → Fin (n a) → ℝ) (commonRank : ℝ)
    (hmass : ∀ a, (datum a).totalRamification (x a) = commonRank) :
    fusionQuadratic genus datum (capacityRay datum commonRank) commonRank ≤
      fusionQuadratic genus datum x commonRank := by
  rw [fusionQuadratic_capacityRay hNonempty genus datum commonRank,
    fusionQuadratic_eq_centered_eulerCapacity hNonempty genus datum x commonRank hmass]
  exact le_add_of_nonneg_left (centeredEnergy_nonneg datum x)

/-- Lorentz phase: a negative Euler--capacity gap is attained by the simultaneous capacity ray. -/
theorem fusionQuadratic_capacityRay_neg_of_eulerCapacityGap_neg {m : ℕ}
    {n : Fin m → ℕ} (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin m) → CertifiedFissionDatum (n a)) {commonRank : ℝ}
    (hmass : commonRank ≠ 0) (hgap : eulerCapacityGap genus datum < 0) :
    fusionQuadratic genus datum (capacityRay datum commonRank) commonRank < 0 := by
  rw [fusionQuadratic_capacityRay hNonempty genus datum commonRank]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hmass) hgap

/-! ## The quadratic form on the physical rank fibre product -/

/-- Ambient family of local Stokes modes for a nonempty puncture set. -/
abbrev GlobalMode {m : ℕ} (n : Fin (m + 1) → ℕ) :=
  (a : Fin (m + 1)) → Fin (n a) → ℝ

/-- Compatible global modes: every puncture carries the same physical rank. -/
def compatibleModes {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a)) :
    Submodule ℝ (GlobalMode n) where
  carrier := {x | ∀ a,
    (datum a).totalRamification (x a) =
      (datum 0).totalRamification (x 0)}
  zero_mem' := by
    intro a
    simp [CertifiedFissionDatum.totalRamification]
  add_mem' := by
    intro x y hx hy a
    change (datum a).massLinear (x a + y a) =
      (datum 0).massLinear (x 0 + y 0)
    rw [map_add, map_add]
    simpa only [CertifiedFissionDatum.massLinear_apply] using
      congrArg₂ (· + ·) (hx a) (hy a)
  smul_mem' := by
    intro c x hx a
    change (datum a).massLinear (c • x a) =
      (datum 0).massLinear (c • x 0)
    rw [map_smul, map_smul]
    simpa only [CertifiedFissionDatum.massLinear_apply] using
      congrArg (c • ·) (hx a)

/-- Projection of a compatible global mode to one puncture. -/
noncomputable def localProjection {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (a : Fin (m + 1)) :
    compatibleModes datum →ₗ[ℝ] (Fin (n a) → ℝ) :=
  (LinearMap.proj a).comp (compatibleModes datum).subtype

/-- The common physical rank, read at the first puncture. -/
noncomputable def commonRankLinear {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a)) :
    compatibleModes datum →ₗ[ℝ] ℝ :=
  (datum 0).massLinear.comp (localProjection datum 0)

theorem compatible_totalRamification {m : ℕ} {n : Fin (m + 1) → ℕ}
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (x : compatibleModes datum) (a : Fin (m + 1)) :
    (datum a).totalRamification (x.1 a) = commonRankLinear datum x := by
  exact x.2 a

/-- The actual global quadratic form, restricted to compatible physical-rank modes. -/
noncomputable def fusionForm {m : ℕ} {n : Fin (m + 1) → ℕ} (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a)) :
    QuadraticForm ℝ (compatibleModes datum) :=
  (∑ a, (datum a).cartanForm.comp (localProjection datum a)) +
    (2 * (1 - (genus : ℝ) - ((m + 1 : ℕ) : ℝ))) •
      (QuadraticMap.sq.comp (commonRankLinear datum))

theorem fusionForm_apply {m : ℕ} {n : Fin (m + 1) → ℕ} (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (x : compatibleModes datum) :
    fusionForm genus datum x = fusionQuadratic genus datum x.1
      (commonRankLinear datum x) := by
  rw [fusionForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.smul_apply, QuadraticMap.comp_apply, QuadraticMap.sq_apply]
  simp only [smul_eq_mul]
  change (∑ a, (datum a).cartanForm (x.1 a)) +
      2 * (1 - (genus : ℝ) - ((m + 1 : ℕ) : ℝ)) *
        (commonRankLinear datum x * commonRankLinear datum x) = _
  simp only [CertifiedFissionDatum.cartanForm_apply, fusionQuadratic, localCartanSum]
  ring

/-- Form-level Euler--capacity decomposition on the physical rank fibre product. -/
theorem fusionForm_eq_centered_eulerCapacity
    {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (x : compatibleModes datum) :
    fusionForm genus datum x = centeredEnergy datum x.1 +
      commonRankLinear datum x ^ 2 * eulerCapacityGap genus datum := by
  rw [fusionForm_apply]
  exact fusionQuadratic_eq_centered_eulerCapacity hNonempty genus datum x.1
    (commonRankLinear datum x) (compatible_totalRamification datum x)

/-- **Global one-port index bound.**  On the physical rank fibre product the Euler--fusion
form has at most one negative square, for arbitrary genus, puncture count, and local sizes. -/
theorem fusionForm_sigNeg_le_one {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a)) :
    sigNeg (fusionForm genus datum) ≤ 1 := by
  let gap : ℝ := eulerCapacityGap genus datum
  let ell : compatibleModes datum →ₗ[ℝ] ℝ :=
    (LinearMap.lsmul ℝ ℝ (Real.sqrt (max 0 (-gap)))).comp
      (commonRankLinear datum)
  apply sigNeg_le_one_of_add_sq_nonneg (fusionForm genus datum) ell
  intro x
  rw [fusionForm_eq_centered_eulerCapacity hNonempty genus datum x]
  change 0 ≤ centeredEnergy datum x.1 + commonRankLinear datum x ^ 2 * gap +
    (Real.sqrt (max 0 (-gap)) * commonRankLinear datum x) ^ 2
  rw [mul_pow, Real.sq_sqrt (le_max_left 0 (-gap))]
  by_cases hgap : 0 ≤ gap
  · rw [max_eq_left (neg_nonpos.mpr hgap)]
    nlinarith [centeredEnergy_nonneg datum x.1,
      mul_nonneg (sq_nonneg (commonRankLinear datum x)) hgap]
  · rw [max_eq_right (neg_nonneg.mpr (le_of_not_ge hgap))]
    nlinarith [centeredEnergy_nonneg datum x.1]

/-- The simultaneous capacity ray as an element of the compatible fibre product. -/
noncomputable def compatibleCapacityRay {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a)))
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (commonRank : ℝ) : compatibleModes datum :=
  ⟨capacityRay datum commonRank, by
    intro a
    rw [capacityRay_mass hNonempty datum commonRank a,
      capacityRay_mass hNonempty datum commonRank 0]⟩

theorem commonRankLinear_compatibleCapacityRay {m : ℕ}
    {n : Fin (m + 1) → ℕ} (hNonempty : ∀ a, Nonempty (Fin (n a)))
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (commonRank : ℝ) :
    commonRankLinear datum (compatibleCapacityRay hNonempty datum commonRank) = commonRank := by
  exact capacityRay_mass hNonempty datum commonRank 0

/-- In the Lorentz phase the global negative inertia is exactly one. -/
theorem fusionForm_sigNeg_eq_one_of_eulerCapacityGap_neg
    {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (hgap : eulerCapacityGap genus datum < 0) :
    sigNeg (fusionForm genus datum) = 1 := by
  have hupper := fusionForm_sigNeg_le_one hNonempty genus datum
  let ray := compatibleCapacityRay hNonempty datum 1
  have hrank : commonRankLinear datum ray = 1 :=
    commonRankLinear_compatibleCapacityRay hNonempty datum 1
  have hrayNeg : fusionForm genus datum ray < 0 := by
    rw [fusionForm_apply, hrank]
    exact fusionQuadratic_capacityRay_neg_of_eulerCapacityGap_neg hNonempty genus datum
      one_ne_zero hgap
  have hrayNe : ray ≠ 0 := by
    intro hray
    rw [hray, map_zero] at hrank
    norm_num at hrank
  have hlower := sigNeg_pos_of_exists_negativeVector (fusionForm genus datum) hrayNe hrayNeg
  omega

/-- At the affine wall, zero energy forces every local mode onto its capacity ray. -/
theorem centeredVector_eq_zero_of_fusionForm_eq_zero
    {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (hgap : eulerCapacityGap genus datum = 0)
    (x : compatibleModes datum) (hzero : fusionForm genus datum x = 0) :
    ∀ a, (datum a).centeredVector (x.1 a) = 0 := by
  have henergy : centeredEnergy datum x.1 = 0 := by
    rw [fusionForm_eq_centered_eulerCapacity hNonempty genus datum x, hgap] at hzero
    simpa using hzero
  intro a
  by_contra ha
  have hpos := centeredEnergy_pos_of_exists datum x.1 ⟨a, ha⟩
  rw [henergy] at hpos
  exact lt_irrefl 0 hpos

theorem eq_compatibleCapacityRay_of_centeredVector_eq_zero
    {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a)))
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (x : compatibleModes datum)
    (hcenter : ∀ a, (datum a).centeredVector (x.1 a) = 0) :
    x = compatibleCapacityRay hNonempty datum (commonRankLinear datum x) := by
  apply Subtype.ext
  funext a
  change x.1 a = capacityRay datum (commonRankLinear datum x) a
  calc
    x.1 a = (datum a).centeredVector (x.1 a) +
        ((datum a).totalRamification (x.1 a) / (datum a).capacity) •
          (datum a).capacityVector :=
      (datum a).centeredVector_decomposition (x.1 a)
    _ = (commonRankLinear datum x / (datum a).capacity) •
          (datum a).capacityVector := by
      rw [hcenter a, compatible_totalRamification datum x a, zero_add]
    _ = capacityRay datum (commonRankLinear datum x) a := rfl

/-- Exact affine null-line classification: every zero mode is the simultaneous capacity ray with
its own common rank. -/
theorem fusionForm_eq_zero_iff_eq_compatibleCapacityRay
    {m : ℕ} {n : Fin (m + 1) → ℕ}
    (hNonempty : ∀ a, Nonempty (Fin (n a))) (genus : ℕ)
    (datum : (a : Fin (m + 1)) → CertifiedFissionDatum (n a))
    (hgap : eulerCapacityGap genus datum = 0)
    (x : compatibleModes datum) :
    fusionForm genus datum x = 0 ↔
      x = compatibleCapacityRay hNonempty datum (commonRankLinear datum x) := by
  constructor
  · intro hzero
    exact eq_compatibleCapacityRay_of_centeredVector_eq_zero hNonempty datum x
      (centeredVector_eq_zero_of_fusionForm_eq_zero hNonempty genus datum hgap x hzero)
  · intro hx
    rw [fusionForm_eq_centered_eulerCapacity hNonempty genus datum x, hgap,
      mul_zero, add_zero]
    rw [centeredEnergy]
    apply Finset.sum_eq_zero
    intro a _
    have hxa : (datum a).centeredVector (x.1 a) = 0 := by
      rw [hx]
      exact capacityRay_centered hNonempty datum (commonRankLinear datum x) a
    rw [hxa]
    simp [CertifiedFissionDatum.positiveQuadratic, FiniteQuadratic.qform]

end EulerFusionCapacity
end IrregularStokes
end GaloisForLFunctions
