import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WeilEnergyIsUnboundedAtEveryAperture

/-!
# Finite linear degree descriptions cannot supply Bézout

Every finite-dimensional linear reading of positive-aperture scaling cycles has a primitive
negative-square direction in its kernel. Self-intersection is consequently unbounded below
on each affine reading fibre. Any nonempty effective set determined by such a reading fails
Bézout, independently of the rule used to turn its finite readings into membership.
-/

noncomputable section

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

/-- Every finite linear reading misses a primitive negative-square scaling cycle. -/
theorem exists_negative_square_in_finite_reading_ker {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] V) :
    ∃ p : ℝ × ℝ × realTestsAt r, L p = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair p (scalingSubsurface (realTestsAt r)).H = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair p (scalingSubsurface (realTestsAt r)).V = 0 ∧
      (scalingSubsurface (realTestsAt r)).pair p p < 0 := by
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
  obtain ⟨f, hW, hker⟩ := exists_realTestAt_in_ker_weilPair_gt hr 0 ((L.prod d).comp e)
  have hL : L (0, 0, f) = 0 := congrArg Prod.fst hker
  have hH : S.pair (0, 0, f) S.H = 0 := congrArg (fun v => v.2.1) hker
  have hV : S.pair (0, 0, f) S.V = 0 := congrArg (fun v => v.2.2) hker
  refine ⟨(0, 0, f), hL, hH, hV, ?_⟩
  have hδ := scalingSubsurface_defect_self (realTestsAt r) (0, 0, f)
  rw [S.defect_self, hH, hV, mul_zero, zero_mul, zero_sub] at hδ
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

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
