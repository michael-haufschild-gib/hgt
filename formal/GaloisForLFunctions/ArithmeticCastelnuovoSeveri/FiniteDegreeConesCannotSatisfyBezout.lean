import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WeilEnergyIsUnboundedAtEveryAperture

/-!
# Finite linear degree descriptions cannot supply Bézout

Every finite-dimensional linear reading of positive-aperture scaling cycles has a primitive
negative-square direction in its kernel. Self-intersection is consequently unbounded below
on each affine reading fibre. Any nonempty effective set determined by such a reading fails
Bézout, independently of the rule used to turn its finite readings into membership.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- A negative-square kernel direction makes every affine reading fibre unbounded below. -/
theorem self_pair_unbounded_below_on_fibre
    {V : Type*} [AddCommGroup V] [Module ℝ V] (L : C →ₗ[ℝ] V)
    {p : C} (hp : L p = 0) (hpp : S.pair p p < 0) (x : C) (M : ℝ) :
    ∃ y : C, L y = L x ∧ S.pair y y < M := by
  let a := max (S.pair x x - M) 0 + 1
  have ha : 0 < a := by
    dsimp only [a]
    linarith only [le_max_right (S.pair x x - M) 0]
  have hd : 0 < -S.pair p p := by linarith only [hpp]
  let t := Real.sqrt (a / (-S.pair p p))
  have ht : t ^ 2 * (-S.pair p p) = a := by
    rw [show t ^ 2 = a / (-S.pair p p) from Real.sq_sqrt (div_pos ha hd).le,
      div_mul_cancel₀ _ hd.ne']
  have hav : S.pair (x + t • p) (x + t • p) +
      S.pair (x - t • p) (x - t • p) =
      2 * S.pair x x + 2 * t ^ 2 * S.pair p p := by
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hsum : S.pair (x + t • p) (x + t • p) +
      S.pair (x - t • p) (x - t • p) < 2 * M := by
    rw [hav]
    dsimp only [a] at ht
    nlinarith only [ht, le_max_left (S.pair x x - M) 0]
  by_cases hplus : S.pair (x + t • p) (x + t • p) < M
  · refine ⟨x + t • p, ?_, hplus⟩
    rw [map_add, map_smul, hp, smul_zero, add_zero]
  · refine ⟨x - t • p, ?_, ?_⟩
    · rw [map_sub, map_smul, hp, smul_zero, sub_zero]
    · linarith only [hsum, le_of_not_gt hplus]

end PolarSurface

/-- Arbitrarily large source Rayleigh quotients survive every finite reading and both fibre degrees. -/
theorem exists_primitive_source_in_finite_reading_ker_rayleigh {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) (M : ℝ) :
    ∃ f : realTestsAt r, 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * (∫ u : ℝ, (f.1.1 u) ^ 2) < weilPair f.1.1 f.1.1 ∧
      L (0, 0, f) = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair (0, 0, f)
        (scalingSubsurface (realTestsAt r)).H = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair (0, 0, f)
        (scalingSubsurface (realTestsAt r)).V = 0 := by
  let S := scalingSubsurface (realTestsAt r)
  let e : realTestsAt r →ₗ[ℝ] (ℝ × ℝ × realTestsAt r) :=
    { toFun := fun f => (0, 0, f)
      map_add' := fun _ _ => Prod.ext (zero_add 0).symm (Prod.ext (zero_add 0).symm rfl)
      map_smul' := fun c _ =>
        Prod.ext (smul_zero c).symm (Prod.ext (smul_zero c).symm rfl) }
  let d : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (S.pair x S.H, S.pair x S.V)
      map_add' := fun x y => by
        apply Prod.ext
        · exact congrArg (fun k => k S.H) (S.pair.map_add x y)
        · exact congrArg (fun k => k S.V) (S.pair.map_add x y)
      map_smul' := fun c x => by
        apply Prod.ext
        · change S.pair (c • x) S.H = c • S.pair x S.H
          rw [map_smul, LinearMap.smul_apply]
        · change S.pair (c • x) S.V = c • S.pair x S.V
          rw [map_smul, LinearMap.smul_apply] }
  obtain ⟨f, hm, hW, hker⟩ :=
    exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq hr M ((L.prod d).comp e)
  have hL : L (0, 0, f) = 0 := congrArg Prod.fst hker
  have hH : S.pair (0, 0, f) S.H = 0 := congrArg (fun v => v.2.1) hker
  have hV : S.pair (0, 0, f) S.V = 0 := congrArg (fun v => v.2.2) hker
  exact ⟨f, hm, hW, hL, hH, hV⟩

/-- Every finite linear reading misses a primitive negative-square scaling cycle. -/
theorem exists_negative_square_in_finite_reading_ker {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) :
    ∃ p : ℝ × ℝ × realTestsAt r, L p = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair p (scalingSubsurface (realTestsAt r)).H = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair p (scalingSubsurface (realTestsAt r)).V = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair p p < 0 := by
  let S := scalingSubsurface (realTestsAt r)
  obtain ⟨f, -, hW, hL, hH, hV⟩ :=
    exists_primitive_source_in_finite_reading_ker_rayleigh hr L 0
  simp only [zero_mul] at hW
  refine ⟨(0, 0, f), hL, hH, hV, ?_⟩
  have hδ := scalingSubsurface_defect_self (realTestsAt r) (0, 0, f)
  rw [PolarSurface.defect_self, hH, hV] at hδ
  simp only [mul_zero, zero_sub] at hδ
  linarith only [hδ, hW]

/-- Every affine finite-reading fibre has arbitrarily negative self-intersection. -/
theorem scalingSubsurface_self_pair_unbounded_below_on_finite_reading_fibre
    {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) (x : ℝ × ℝ × realTestsAt r) (M : ℝ) :
    ∃ y : ℝ × ℝ × realTestsAt r, L y = L x ∧
      (scalingSubsurface (realTestsAt r)).pair y y < M := by
  obtain ⟨p, hp, -, -, hpp⟩ := exists_negative_square_in_finite_reading_ker hr L
  exact (scalingSubsurface (realTestsAt r)).self_pair_unbounded_below_on_fibre L hp hpp x M

/-- Negative squares occur arbitrarily close in source mass, with all finite readings and fibre degrees fixed. -/
theorem scalingSubsurface_self_pair_unbounded_below_with_small_source_mass
    {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) (x : ℝ × ℝ × realTestsAt r)
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ × ℝ × realTestsAt r, L y = L x ∧
      (scalingSubsurface (realTestsAt r)).pair y (scalingSubsurface (realTestsAt r)).H =
        (scalingSubsurface (realTestsAt r)).pair x (scalingSubsurface (realTestsAt r)).H ∧
      (scalingSubsurface (realTestsAt r)).pair y (scalingSubsurface (realTestsAt r)).V =
        (scalingSubsurface (realTestsAt r)).pair x (scalingSubsurface (realTestsAt r)).V ∧
      (∫ u : ℝ, (y.2.2.1.1 u - x.2.2.1.1 u) ^ 2) < ε ∧
      (scalingSubsurface (realTestsAt r)).pair y y < M := by
  let S := scalingSubsurface (realTestsAt r)
  let a := max (S.pair x x - M) 0 + 1
  obtain ⟨f, hm, hW, hker, hH, hV⟩ :=
    exists_primitive_source_in_finite_reading_ker_rayleigh hr (L.prod (S.pair x)) (2 * a / ε)
  let p : ℝ × ℝ × realTestsAt r := (0, 0, f)
  let m := ∫ u : ℝ, (f.1.1 u) ^ 2
  have hm' : 0 < m := hm
  change S.pair p S.H = 0 at hH
  change S.pair p S.V = 0 at hV
  have hL : L p = 0 := congrArg Prod.fst hker
  have hxp : S.pair x p = 0 := congrArg Prod.snd hker
  have hpx : S.pair p x = 0 := by rw [S.pair_comm, hxp]
  have hpp : S.pair p p = -weilPair f.1.1 f.1.1 := by
    have hδ := scalingSubsurface_defect_self (realTestsAt r) p
    change S.defect p p = weilPair f.1.1 f.1.1 at hδ
    rw [S.defect_self, hH, hV] at hδ
    simp only [mul_zero, zero_sub] at hδ
    linarith only [hδ]
  let t := Real.sqrt (ε / (2 * m))
  have ht2 : t ^ 2 = ε / (2 * m) := Real.sq_sqrt (by positivity)
  have htpos : 0 < t ^ 2 := by rw [ht2]; positivity
  have htm : t ^ 2 * m = ε / 2 := by
    rw [ht2]
    field_simp [hm'.ne']
  have hleft : t ^ 2 * ((2 * a / ε) * m) = a := by
    calc
      _ = (t ^ 2 * m) * (2 * a / ε) := by ring
      _ = a := by rw [htm]; field_simp [ne_of_gt hε]
  have hlarge : a < t ^ 2 * weilPair f.1.1 f.1.1 := by
    have h := mul_lt_mul_of_pos_left hW htpos
    rw [hleft] at h
    exact h
  let y := x + t • p
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · change L (x + t • p) = L x
    rw [map_add, map_smul, hL, smul_zero, add_zero]
  · change S.pair (x + t • p) S.H = S.pair x S.H
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hH, mul_zero, add_zero]
  · change S.pair (x + t • p) S.V = S.pair x S.V
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hV, mul_zero, add_zero]
  · have he : (fun u : ℝ => (y.2.2.1.1 u - x.2.2.1.1 u) ^ 2) =
        fun u : ℝ => t ^ 2 * (f.1.1 u) ^ 2 := by
      funext u
      change (x.2.2.1.1 u + t * f.1.1 u - x.2.2.1.1 u) ^ 2 = _
      ring
    rw [he, integral_const_mul]
    change t ^ 2 * m < ε
    rw [htm]
    linarith only [hε]
  · change S.pair (x + t • p) (x + t • p) < M
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hxp, hpx, hpp, mul_zero, zero_add, add_zero]
    dsimp only [a] at hlarge
    nlinarith only [hlarge, le_max_left (S.pair x x - M) 0]

/-- No nonempty set determined by finitely many linear degree readings satisfies Bézout. -/
theorem finite_reading_preimage_not_bezout {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) (A : Set V)
    (hne : (L ⁻¹' A).Nonempty) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom (L ⁻¹' A) := by
  intro hB
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hyy⟩ :=
    scalingSubsurface_self_pair_unbounded_below_on_finite_reading_fibre hr L x 0
  have hyA : y ∈ L ⁻¹' A := by
    change L y ∈ A
    rw [hy]
    exact hx
  exact (not_lt_of_ge (hB y hyA y hyA)) hyy

/-- The only Bézout set determined by a finite-dimensional linear cycle reading is empty. -/
theorem finite_reading_preimage_bezout_iff_empty {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) (A : Set V) :
    (scalingSubsurface (realTestsAt r)).BezoutAxiom (L ⁻¹' A) ↔ L ⁻¹' A = ∅ := by
  constructor
  · intro hB
    ext x
    constructor
    · intro hx
      exact (finite_reading_preimage_not_bezout hr L A ⟨x, hx⟩ hB).elim
    · intro hx
      exact hx.elim
  · intro he
    rw [he]
    intro x hx
    exact hx.elim

/-- The original, unrestricted scaling surface has negative directions in every finite reading kernel. -/
theorem scalingSurface_exists_negative_square_in_finite_reading_ker
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) :
    ∃ p : ScalingCycle, L p = 0 ∧ scalingSurface.pair p p < 0 := by
  obtain ⟨p, hp, -, -, hpp⟩ := exists_negative_square_in_finite_reading_ker
    (r := 1) zero_lt_one (L.comp (scalingSubsurfaceInclusion (realTestsAt 1)))
  exact ⟨scalingSubsurfaceInclusion (realTestsAt 1) p, hp, hpp⟩

/-- Arbitrarily negative intersection occurs in every finite-reading fibre of the original surface. -/
theorem scalingSurface_self_pair_unbounded_below_on_finite_reading_fibre
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) (x : ScalingCycle) (M : ℝ) :
    ∃ y : ScalingCycle, L y = L x ∧ scalingSurface.pair y y < M := by
  obtain ⟨p, hp, hpp⟩ := scalingSurface_exists_negative_square_in_finite_reading_ker L
  exact scalingSurface.self_pair_unbounded_below_on_fibre L hp hpp x M

/-- On the full scaling surface a finite linear degree description has Bézout only when empty. -/
theorem scalingSurface_finite_reading_preimage_bezout_iff_empty
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) (A : Set V) :
    scalingSurface.BezoutAxiom (L ⁻¹' A) ↔ L ⁻¹' A = ∅ := by
  constructor
  · intro hB
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyy⟩ :=
        scalingSurface_self_pair_unbounded_below_on_finite_reading_fibre L x 0
      have hyA : y ∈ L ⁻¹' A := by
        change L y ∈ A
        rw [hy]
        exact hx
      exact (not_lt_of_ge (hB y hyA y hyA) hyy).elim
    · intro hx
      exact hx.elim
  · intro he
    rw [he]
    intro x hx
    exact hx.elim

/-- No finite linear cycle reading determines self-intersection, even through arbitrary postprocessing. -/
theorem scalingSurface_selfPair_not_finiteLinearReading
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) :
    ¬ ∃ F : V → ℝ, ∀ x : ScalingCycle, scalingSurface.pair x x = F (L x) := by
  rintro ⟨F, hF⟩
  obtain ⟨y, hy, hyy⟩ :=
    scalingSurface_self_pair_unbounded_below_on_finite_reading_fibre L 0 (F 0)
  rw [hF y, hy, map_zero] at hyy
  exact (lt_irrefl _ hyy)

/-- The scaling intersection form cannot descend through a finite-dimensional linear quotient. -/
theorem scalingSurface_pairing_not_finiteLinearQuotient
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) :
    ¬ ∃ B : V → V → ℝ, ∀ x y : ScalingCycle, scalingSurface.pair x y = B (L x) (L y) := by
  rintro ⟨B, hB⟩
  exact scalingSurface_selfPair_not_finiteLinearReading L ⟨fun v => B v v, fun x => hB x x⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
