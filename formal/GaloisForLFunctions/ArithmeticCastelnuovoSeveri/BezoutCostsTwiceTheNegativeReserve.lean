import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticMajorantsSupplyBezout

/-!
# Bézout costs twice the negative reserve

For a positive quadratic fibre reserve `R`, the source threshold `defect + 2 R`
has Bézout on the original surface exactly when `defect + R` is nonnegative.
This compares source effectivity with compensation of the intersection pairing.
Graded RR permits this positive extra reserve only when it vanishes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface
variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- Source threshold formed by adding twice a quadratic reserve to the original defect. -/
def doubledReserveEnergy (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (x : C) : ℝ :=
  S.defect x x + 2 * R x x

private theorem doubled_reserve_even (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (x : C) :
    S.doubledReserveEnergy R (-x) = S.doubledReserveEnergy R x := by
  simp only [doubledReserveEnergy, S.defect_neg_self, map_neg, LinearMap.neg_apply, neg_neg]

private theorem doubled_reserve_fibre
    (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, R x y = R y x)
    (hH : ∀ x, R x S.H = 0) (hV : ∀ x, R x S.V = 0)
    (x : C) (a b : ℝ) :
    S.doubledReserveEnergy R (x + a • S.H + b • S.V) = S.doubledReserveEnergy R x := by
  have hHl (y : C) : R S.H y = 0 := (hs S.H y).trans (hH y)
  have hVl (y : C) : R S.V y = 0 := (hs S.V y).trans (hV y)
  have hdH (y : C) : S.defect y S.H = 0 := by
    simp only [defect, polar, S.pair_H_H, S.pair_H_V, mul_one, mul_zero, add_zero, sub_self]
  have hdV (y : C) : S.defect y S.V = 0 := by
    simp only [defect, polar, S.pair_V_H, S.pair_V_V, mul_one, mul_zero, zero_add, sub_self]
  have hdHl (y : C) : S.defect S.H y = 0 := (S.defect_comm S.H y).trans (hdH y)
  have hdVl (y : C) : S.defect S.V y = 0 := (S.defect_comm S.V y).trans (hdV y)
  change S.defectLinearMap (x + a • S.H + b • S.V) (x + a • S.H + b • S.V) +
    2 * R (x + a • S.H + b • S.V) (x + a • S.H + b • S.V) = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hd (u v : C) : S.defectLinearMap u v = S.defect u v := rfl
  simp only [hd, hdH, hdV, hdHl, hdVl, hH, hV, hHl, hVl, mul_zero, add_zero,
    doubledReserveEnergy]

private theorem negative_diagonal_le_reserve (d p : ℝ) (hp : 0 ≤ p) (hsq : d ^ 2 ≤ p * p) :
    -d ≤ p := by
  by_contra h
  have h1 : 0 < -d - p := by linarith only [lt_of_not_ge h]
  have h2 : 0 < -d + p := by linarith only [h1, hp]
  have hm := mul_pos h1 h2
  nlinarith only [hm, hsq]

/-- Graded original-surface Bézout is exactly the diagonal floor paid by half the added reserve. -/
theorem gradedSourceCone_doubledReserve_bezout_iff
    (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, R x y = R y x)
    (hnn : ∀ x, 0 ≤ R x x) (hH : ∀ x, R x S.H = 0) (hV : ∀ x, R x S.V = 0) :
    S.BezoutAxiom (S.gradedSourceCone (S.doubledReserveEnergy R)) ↔
      ∀ x, 0 ≤ S.defect x x + R x x := by
  rw [S.gradedSourceCone_bezout_iff (S.doubled_reserve_even R)
    (S.doubled_reserve_fibre R hs hH hV)]
  constructor
  · rintro ⟨hpos, hcs⟩ x
    have hl := negative_diagonal_le_reserve (S.defect x x)
      (S.doubledReserveEnergy R x) (hpos x) (hcs x x)
    unfold doubledReserveEnergy at hl
    linarith only [hl]
  · intro hfloor
    have hpos (x : C) : 0 ≤ S.doubledReserveEnergy R x := by
      have hr := hnn x
      have hf := hfloor x
      unfold doubledReserveEnergy
      linarith only [hr, hf]
    refine ⟨hpos, ?_⟩
    let Q := S.defectLinearMap + (2 : ℝ) • R
    have he (x y : C) : Q x y = S.defect x y + 2 * R x y := rfl
    have hQ (x y : C) : Q x y = Q y x := by rw [he, he, S.defect_comm, hs]
    have hup (x : C) : S.defect x x ≤ Q x x := by rw [he]; linarith only [hnn x]
    have hlo (x : C) : -S.defect x x ≤ Q x x := by rw [he]; linarith only [hfloor x]
    exact S.defect_sq_le_of_quadratic_majorant Q hQ hup hlo

/-- Closed source Bézout has the same exact doubled-reserve boundary. -/
theorem sourceCone_doubledReserve_bezout_iff
    (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, R x y = R y x)
    (hnn : ∀ x, 0 ≤ R x x) (hH : ∀ x, R x S.H = 0) (hV : ∀ x, R x S.V = 0) :
    S.BezoutAxiom (S.sourceCone (S.doubledReserveEnergy R)) ↔
      ∀ x, 0 ≤ S.defect x x + R x x := by
  constructor
  · intro hB
    let P := fun x => max (S.doubledReserveEnergy R x) 0
    have hBP : S.BezoutAxiom (S.sourceCone P) := by
      rw [S.sourceCone_eq_positivePart] at hB
      exact hB
    have hpEven (x : C) : P (-x) = P x := by
      dsimp only [P]
      rw [S.doubled_reserve_even]
    have hpFib (x : C) (a b : ℝ) : P (x + a • S.H + b • S.V) = P x := by
      dsimp only [P]
      rw [S.doubled_reserve_fibre R hs hH hV]
    have hcs := (S.sourceCone_bezout_iff_defect_sq_le (fun x => le_max_right _ _)
      hpEven hpFib).mp hBP
    intro x
    have hpos : 0 ≤ S.doubledReserveEnergy R x := by
      by_contra hnot
      have ht := lt_of_not_ge hnot
      have hsq := hcs x x
      rw [max_eq_right ht.le, zero_mul] at hsq
      have hzero : S.defect x x = 0 := by nlinarith only [hsq, sq_nonneg (S.defect x x)]
      unfold doubledReserveEnergy at ht
      rw [hzero, zero_add] at ht
      linarith only [ht, hnn x]
    have hsq := hcs x x
    rw [max_eq_left hpos] at hsq
    have hl := negative_diagonal_le_reserve (S.defect x x)
      (S.doubledReserveEnergy R x) hpos hsq
    unfold doubledReserveEnergy at hl
    linarith only [hl]
  · intro hfloor
    have hB := (S.gradedSourceCone_doubledReserve_bezout_iff R hs hnn hH hV).mpr hfloor
    intro x hx y hy
    exact hB x (S.sourceCone_subset_gradedSourceCone _ hx) y
      (S.sourceCone_subset_gradedSourceCone _ hy)

/-- Original-pairing Bézout with twice the reserve equals Hodge index after one reserve compensation. -/
theorem sourceCone_doubledReserve_bezout_iff_compensated_hodgeIndex
    (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, R x y = R y x)
    (hnn : ∀ x, 0 ≤ R x x) (hH : ∀ x, R x S.H = 0) (hV : ∀ x, R x S.V = 0) :
    S.BezoutAxiom (S.sourceCone (S.doubledReserveEnergy R)) ↔
      (S.compensatedSurface R hs hH hV).HodgeIndex := by
  rw [S.sourceCone_doubledReserve_bezout_iff R hs hnn hH hV,
    S.compensatedSurface_hodgeIndex_iff]
  apply forall_congr'
  intro x
  constructor <;> intro h <;> linarith only [h]

/-- A nonnegative extra quadratic reserve is compatible with graded RR exactly when it vanishes. -/
theorem gradedSourceCone_doubledReserve_riemannRoch_iff
    (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, R x y = R y x)
    (hnn : ∀ x, 0 ≤ R x x) (hH : ∀ x, R x S.H = 0) (hV : ∀ x, R x S.V = 0) :
    S.RiemannRochAxiom (S.gradedSourceCone (S.doubledReserveEnergy R)) ↔
      ∀ x, R x x = 0 := by
  rw [S.gradedSourceCone_riemannRoch_iff_le_defect_without_symmetry
    (S.doubled_reserve_fibre R hs hH hV)]
  constructor
  · intro h x
    have hx := h x
    unfold doubledReserveEnergy at hx
    linarith only [hx, hnn x]
  · intro h x
    simp only [doubledReserveEnergy, h x, mul_zero, add_zero, le_refl]

/-- Closed RR additionally requires nonnegative original defect. -/
theorem sourceCone_doubledReserve_riemannRoch_iff
    (R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, R x y = R y x)
    (hnn : ∀ x, 0 ≤ R x x) (hH : ∀ x, R x S.H = 0) (hV : ∀ x, R x S.V = 0) :
    S.RiemannRochAxiom (S.sourceCone (S.doubledReserveEnergy R)) ↔
      (∀ x, R x x = 0) ∧ ∀ x, 0 ≤ S.defect x x := by
  rw [S.sourceCone_riemannRoch_iff_positivePart_le_defect
    (S.doubled_reserve_fibre R hs hH hV)]
  constructor
  · intro h
    refine ⟨?_, fun x => (le_max_right _ _).trans (h x)⟩
    intro x
    have hl := (le_max_left _ _).trans (h x)
    unfold doubledReserveEnergy at hl
    linarith only [hl, hnn x]
  · rintro ⟨hR, hd⟩ x
    simp only [doubledReserveEnergy, hR x, mul_zero, add_zero, max_eq_left (hd x), le_refl]


/-- For a scalar quadratic reserve, the exact Bézout floor uses half its coefficient. -/
theorem sourceCone_defect_add_scalar_reserve_bezout_iff
    (M : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, M x y = M y x)
    (hnn : ∀ x, 0 ≤ M x x) (hH : ∀ x, M x S.H = 0) (hV : ∀ x, M x S.V = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    S.BezoutAxiom (S.sourceCone (fun x => S.defect x x + κ * M x x)) ↔
      ∀ x, 0 ≤ S.defect x x + (κ / 2) * M x x := by
  let R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ := (κ / 2) • M
  have hRs (x y : C) : R x y = R y x := by
    change (κ / 2) * M x y = (κ / 2) * M y x
    rw [hs]
  have hRn (x : C) : 0 ≤ R x x :=
    mul_nonneg (div_nonneg hκ (by norm_num)) (hnn x)
  have hRH (x : C) : R x S.H = 0 := by
    change (κ / 2) * M x S.H = 0
    rw [hH, mul_zero]
  have hRV (x : C) : R x S.V = 0 := by
    change (κ / 2) * M x S.V = 0
    rw [hV, mul_zero]
  have he : S.doubledReserveEnergy R = fun x => S.defect x x + κ * M x x := by
    funext x
    change S.defect x x + 2 * ((κ / 2) * M x x) = _
    ring
  have h := S.sourceCone_doubledReserve_bezout_iff R hRs hRn hRH hRV
  rw [he] at h
  exact h

/-- The same exact scalar coefficient governs graded source effectivity. -/
theorem gradedSourceCone_defect_add_scalar_reserve_bezout_iff
    (M : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hs : ∀ x y, M x y = M y x)
    (hnn : ∀ x, 0 ≤ M x x) (hH : ∀ x, M x S.H = 0) (hV : ∀ x, M x S.V = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    S.BezoutAxiom (S.gradedSourceCone (fun x => S.defect x x + κ * M x x)) ↔
      ∀ x, 0 ≤ S.defect x x + (κ / 2) * M x x := by
  let R : C →ₗ[ℝ] C →ₗ[ℝ] ℝ := (κ / 2) • M
  have hRs (x y : C) : R x y = R y x := by
    change (κ / 2) * M x y = (κ / 2) * M y x
    rw [hs]
  have hRn (x : C) : 0 ≤ R x x :=
    mul_nonneg (div_nonneg hκ (by norm_num)) (hnn x)
  have hRH (x : C) : R x S.H = 0 := by
    change (κ / 2) * M x S.H = 0
    rw [hH, mul_zero]
  have hRV (x : C) : R x S.V = 0 := by
    change (κ / 2) * M x S.V = 0
    rw [hV, mul_zero]
  have he : S.doubledReserveEnergy R = fun x => S.defect x x + κ * M x x := by
    funext x
    change S.defect x x + 2 * ((κ / 2) * M x x) = _
    ring
  have h := S.gradedSourceCone_doubledReserve_bezout_iff R hRs hRn hRH hRV
  rw [he] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface
