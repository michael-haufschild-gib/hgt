import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GradedSourceConeBoundaryRigidity

/-!
# Riemann–Roch does not require source symmetry

Every real polar capacity occurs at strictly positive ample degree. This makes the graded
RR boundary pointwise, even for an asymmetric reserve. Nonnegative-fibre cones only see the
positive part of the reserve. Consequently simultaneous RR and Bézout force exactly the
nonnegative defect, with no initial symmetry or sign assumption.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

private theorem exists_degrees_of_capacity (c : ℝ) :
    ∃ a b : ℝ, 0 < a + b ∧ 2 * a * b = c := by
  let b := |c| + 1
  have hb : 0 < b := by dsimp only [b]; linarith only [abs_nonneg c]
  let a := c / (2 * b)
  have hab : 2 * a * b = c := by
    dsimp only [a]
    field_simp [ne_of_gt hb]
  refine ⟨a, b, ?_, hab⟩
  by_contra h
  have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hb.le
  dsimp only [b] at hm hab
  nlinarith only [hm, hab, neg_abs_le c, abs_nonneg c, sq_nonneg |c|]

/-- Every fibre-invariant signed reserve has RR exactly below the diagonal defect. -/
theorem gradedSourceCone_riemannRoch_iff_le_defect_without_symmetry {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (S.gradedSourceCone Φ) ↔ ∀ x : C, Φ x ≤ S.defect x x := by
  constructor
  · intro hRR x
    by_contra h
    have hlt := lt_of_not_ge h
    let c := (Φ x + S.defect x x) / 2
    obtain ⟨a, b, hab, hc⟩ := exists_degrees_of_capacity c
    let y := S.withFibreDegrees x a b
    have hA : 0 < S.pair y S.ample := by
      rw [S.pair_ample, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
      exact hab
    have hcap : S.polar y y = c := by
      rw [S.polar_self, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
      exact hc
    have hd : S.defect y y = S.defect x x := S.defect_withFibreDegrees x x a b a b
    have hyy : 0 < S.pair y y := by
      rw [defect, hcap] at hd
      dsimp only [c] at hd
      linarith only [hd, hlt]
    rcases hRR y hyy with hy | hy
    · have hΦ := ((S.mem_gradedSourceCone_iff Φ y).mp hy).2
      rw [S.source_withFibreDegrees hfib, hcap] at hΦ
      dsimp only [c] at hΦ
      linarith only [hΦ, hlt]
    · have hneg := ((S.mem_gradedSourceCone_iff Φ (-y)).mp hy).1
      rw [S.pair_neg_left] at hneg
      linarith only [hneg, hA]
  · intro hle x hx
    have hcap (y : C) (hy : 0 < S.pair y y) : Φ y ≤ S.polar y y := by
      have h := hle y
      rw [defect] at h
      linarith only [h, hy]
    rcases le_total 0 (S.pair x S.ample) with hA | hA
    · exact Or.inl ⟨hA, hcap x hx⟩
    · refine Or.inr ⟨?_, hcap (-x) ?_⟩
      · rw [S.pair_neg_left]
        exact neg_nonneg.mpr hA
      · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hx

/-- A nonnegative reserve needs no evenness assumption in the RR classification. -/
theorem sourceCone_riemannRoch_iff_le_defect_without_symmetry {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (S.sourceCone Φ) ↔ ∀ x : C, Φ x ≤ S.defect x x := by
  rw [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
  exact S.gradedSourceCone_riemannRoch_iff_le_defect_without_symmetry hfib

/-- Negative reserve values are invisible on the nonnegative-fibre quadrant. -/
theorem sourceCone_eq_positivePart (Φ : C → ℝ) :
    S.sourceCone Φ = S.sourceCone (fun x => max (Φ x) 0) := by
  ext x
  rw [S.mem_sourceCone_iff, S.mem_sourceCone_iff]
  constructor
  · rintro ⟨hH, hV, hΦ⟩
    refine ⟨hH, hV, max_le hΦ ?_⟩
    rw [S.polar_self]
    exact mul_nonneg (mul_nonneg (by norm_num) hH) hV
  · rintro ⟨hH, hV, hΦ⟩
    exact ⟨hH, hV, (le_max_left _ _).trans hΦ⟩

theorem strictSourceCone_eq_positivePart (Φ : C → ℝ) :
    S.strictSourceCone Φ = S.strictSourceCone (fun x => max (Φ x) 0) := by
  ext x
  rw [S.mem_strictSourceCone_iff, S.mem_strictSourceCone_iff]
  constructor
  · rintro ⟨hH, hV, hΦ⟩
    refine ⟨hH, hV, max_lt hΦ ?_⟩
    rw [S.polar_self]
    exact mul_pos (mul_pos (by norm_num) hH) hV
  · rintro ⟨hH, hV, hΦ⟩
    exact ⟨hH, hV, (le_max_left _ _).trans_lt hΦ⟩

/-- Closed source RR is exactly positive-part domination by the defect. -/
theorem sourceCone_riemannRoch_iff_positivePart_le_defect {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (S.sourceCone Φ) ↔ ∀ x : C, max (Φ x) 0 ≤ S.defect x x := by
  rw [S.sourceCone_eq_positivePart]
  exact S.sourceCone_riemannRoch_iff_le_defect_without_symmetry
    (fun x => le_max_right _ _) (fun x a b => congrArg (fun t => max t 0) (hfib x a b))

private theorem strictSourceCone_riemannRoch_without_symmetry {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (hle : ∀ x : C, Φ x ≤ S.defect x x) :
    S.RiemannRochAxiom (S.strictSourceCone Φ) := by
  have hdnn : ∀ x : C, 0 ≤ S.defect x x := fun x => (hnn x).trans (hle x)
  have hdeven : ∀ x : C, S.defect (-x) (-x) = S.defect x x := by
    intro x
    simp only [defect, S.polar_neg_self, map_neg, LinearMap.neg_apply, neg_neg]
  have hRR := S.strictSourceCone_riemannRoch_of_le_defect hdeven hdnn (fun _ => le_rfl)
  have hsub : S.strictSourceCone (fun x => S.defect x x) ⊆ S.strictSourceCone Φ := by
    intro x hx
    rw [S.mem_strictSourceCone_iff] at hx ⊢
    exact ⟨hx.1, hx.2.1, (hle x).trans_lt hx.2.2⟩
  intro x hx
  exact (hRR x hx).imp (fun h => hsub h) (fun h => hsub h)

theorem strictSourceCone_riemannRoch_iff_positivePart_le_defect {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (S.strictSourceCone Φ) ↔
      ∀ x : C, max (Φ x) 0 ≤ S.defect x x := by
  constructor
  · intro hRR
    apply (S.sourceCone_riemannRoch_iff_positivePart_le_defect hfib).mp
    intro x hx
    exact (hRR x hx).imp (fun h => S.strictSourceCone_subset_sourceCone Φ h)
      (fun h => S.strictSourceCone_subset_sourceCone Φ h)
  · intro hle
    rw [S.strictSourceCone_eq_positivePart]
    exact S.strictSourceCone_riemannRoch_without_symmetry (fun x => le_max_right _ _) hle

/-- The exact nonnegative source boundary is forced without assuming source symmetry. -/
theorem sourceCone_riemannRoch_and_bezout_iff_without_symmetry {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.sourceCone Φ) ∧ S.BezoutAxiom (S.sourceCone Φ)) ↔
      ∀ x : C, Φ x = S.defect x x := by
  constructor
  · rintro ⟨hRR, hB⟩ x
    exact le_antisymm
      ((S.sourceCone_riemannRoch_iff_le_defect_without_symmetry hnn hfib).mp hRR x)
      (S.defect_le_source_of_sourceCone_bezout hnn hfib hB x)
  · intro heq
    have hH := S.hodgeIndex_iff_defect_nonneg.mpr (fun x => (heq x) ▸ hnn x)
    exact ⟨(S.sourceCone_riemannRoch_iff_le_defect_without_symmetry hnn hfib).mpr
      (fun x => (heq x).le), S.sourceCone_bezout_of_defect_le hH (fun x => (heq x).ge)⟩

/-- Signed closed reserves have both axioms exactly when their positive part is the defect. -/
theorem sourceCone_riemannRoch_and_bezout_iff_positivePart_eq_defect {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.sourceCone Φ) ∧ S.BezoutAxiom (S.sourceCone Φ)) ↔
      ∀ x : C, max (Φ x) 0 = S.defect x x := by
  rw [S.sourceCone_eq_positivePart]
  exact S.sourceCone_riemannRoch_and_bezout_iff_without_symmetry
    (fun x => le_max_right _ _) (fun x a b => congrArg (fun t => max t 0) (hfib x a b))

theorem strictSourceCone_riemannRoch_and_bezout_iff_positivePart_eq_defect {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.strictSourceCone Φ) ∧
      S.BezoutAxiom (S.strictSourceCone Φ)) ↔
      ∀ x : C, max (Φ x) 0 = S.defect x x := by
  have hfib' := fun x a b => congrArg (fun t => max t 0) (hfib x a b)
  constructor
  · rintro ⟨hRR, hB⟩ x
    have hle := (S.strictSourceCone_riemannRoch_iff_positivePart_le_defect hfib).mp hRR x
    rw [S.strictSourceCone_eq_positivePart] at hB
    exact le_antisymm hle
      (S.defect_le_source_of_strictSourceCone_bezout (fun x => le_max_right _ _) hfib' hB x)
  · intro heq
    have hH := S.hodgeIndex_iff_defect_nonneg.mpr
      (fun x => (heq x) ▸ le_max_right (Φ x) 0)
    refine ⟨(S.strictSourceCone_riemannRoch_iff_positivePart_le_defect hfib).mpr
      (fun x => (heq x).le), ?_⟩
    rw [S.strictSourceCone_eq_positivePart]
    exact S.strictSourceCone_bezout_of_defect_le hH (fun x => (heq x).ge)

/-- Graded RR and Bézout force the exact nonnegative defect, including its symmetry. -/
theorem gradedSourceCone_riemannRoch_and_bezout_iff_without_symmetry {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.gradedSourceCone Φ) ∧
      S.BezoutAxiom (S.gradedSourceCone Φ)) ↔
      (∀ x : C, 0 ≤ Φ x) ∧ ∀ x : C, Φ x = S.defect x x := by
  constructor
  · rintro ⟨hRR, hB⟩
    have hnn := S.source_nonneg_of_gradedSourceCone_bezout hfib hB
    refine ⟨hnn, (S.sourceCone_riemannRoch_and_bezout_iff_without_symmetry hnn hfib).mp ?_⟩
    rw [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
    exact ⟨hRR, hB⟩
  · rintro ⟨hnn, heq⟩
    rw [← S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
    exact (S.sourceCone_riemannRoch_and_bezout_iff_without_symmetry hnn hfib).mpr heq

/-- Without symmetry, Bézout bounds only the positive part of each mixed defect. -/
theorem sourceCone_bezout_iff_positiveDefect_sq_le {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (S.sourceCone Φ) ↔
      ∀ x y : C, max (S.defect x y) 0 ^ 2 ≤ Φ x * Φ y := by
  constructor
  · intro hB x y
    let p := Real.sqrt (Φ x / 2)
    let q := Real.sqrt (Φ y / 2)
    have hp : 0 ≤ p := Real.sqrt_nonneg _
    have hq : 0 ≤ q := Real.sqrt_nonneg _
    have hp2 : p ^ 2 = Φ x / 2 := Real.sq_sqrt (div_nonneg (hnn x) (by norm_num))
    have hq2 : q ^ 2 = Φ y / 2 := Real.sq_sqrt (div_nonneg (hnn y) (by norm_num))
    have hx : S.withFibreDegrees x p p ∈ S.sourceCone Φ := by
      rw [S.mem_sourceCone_iff, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
        S.source_withFibreDegrees hfib, S.polar_self, S.withFibreDegrees_pair_H,
        S.withFibreDegrees_pair_V]
      exact ⟨hp, hp, by nlinarith only [hp2]⟩
    have hy : S.withFibreDegrees y q q ∈ S.sourceCone Φ := by
      rw [S.mem_sourceCone_iff, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
        S.source_withFibreDegrees hfib, S.polar_self, S.withFibreDegrees_pair_H,
        S.withFibreDegrees_pair_V]
      exact ⟨hq, hq, by nlinarith only [hq2]⟩
    have hpair := hB _ hx _ hy
    rw [S.pair_withFibreDegrees] at hpair
    have hsq : (p * q + p * q) ^ 2 = Φ x * Φ y := by
      calc (p * q + p * q) ^ 2 = 4 * p ^ 2 * q ^ 2 := by ring
        _ = Φ x * Φ y := by rw [hp2, hq2]; ring
    by_cases hδ : 0 ≤ S.defect x y
    · rw [max_eq_left hδ]
      have hsum : 0 ≤ p * q + p * q + S.defect x y := by
        nlinarith only [mul_nonneg hp hq, hδ]
      nlinarith only [hsq, mul_nonneg hpair hsum]
    · rw [max_eq_right (le_of_not_ge hδ), zero_pow (by decide)]
      exact mul_nonneg (hnn x) (hnn y)
  · intro hcs x hx y hy
    obtain ⟨hxH, hxV, hxΦ⟩ := (S.mem_sourceCone_iff Φ x).mp hx
    obtain ⟨hyH, hyV, hyΦ⟩ := (S.mem_sourceCone_iff Φ y).mp hy
    have hpx : 0 ≤ S.polar x x := (hnn x).trans hxΦ
    have hpxy : 0 ≤ S.polar x y :=
      add_nonneg (mul_nonneg hxH hyV) (mul_nonneg hxV hyH)
    have hpolar : S.polar x x * S.polar y y ≤ S.polar x y ^ 2 := by
      have hdet := sq_nonneg (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H)
      dsimp only [polar]
      nlinarith only [hdet]
    by_contra hpair
    have hlt : S.polar x y < S.defect x y := by
      dsimp only [defect]
      linarith only [lt_of_not_ge hpair]
    have hbound := (hcs x y).trans ((mul_le_mul hxΦ hyΦ (hnn y) hpx).trans hpolar)
    rw [max_eq_left (hpxy.trans hlt.le)] at hbound
    have hsum : 0 < S.defect x y + S.polar x y := by linarith only [hlt, hpxy]
    nlinarith only [hbound, mul_pos (sub_pos.mpr hlt) hsum]

/-- The complete signed, asymmetric source Bézout criterion. -/
theorem sourceCone_bezout_iff_positiveParts {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (S.sourceCone Φ) ↔
      ∀ x y : C, max (S.defect x y) 0 ^ 2 ≤ max (Φ x) 0 * max (Φ y) 0 := by
  rw [S.sourceCone_eq_positivePart]
  exact S.sourceCone_bezout_iff_positiveDefect_sq_le
    (fun x => le_max_right _ _) (fun x a b => congrArg (fun t => max t 0) (hfib x a b))

theorem gradedSourceCone_bezout_iff_without_symmetry {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (S.gradedSourceCone Φ) ↔
      (∀ x : C, 0 ≤ Φ x) ∧ ∀ x y : C, max (S.defect x y) 0 ^ 2 ≤ Φ x * Φ y := by
  constructor
  · intro hB
    have hnn := S.source_nonneg_of_gradedSourceCone_bezout hfib hB
    refine ⟨hnn, (S.sourceCone_bezout_iff_positiveDefect_sq_le hnn hfib).mp ?_⟩
    rwa [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
  · rintro ⟨hnn, hcs⟩
    rw [← S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
    exact (S.sourceCone_bezout_iff_positiveDefect_sq_le hnn hfib).mpr hcs

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface
