import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AllApertureSourceRiemannRochAndCoercivityLaws

/-!
# Boundary rigidity of source effectivity

For a nonnegative source energy invariant under fibre translations, Riemann–Roch requires
the source energy to lie below the intersection defect. Bézout requires the reverse inequality:
translate each source to the boundary where its polar capacity equals its source energy, then
test its self-intersection. Consequently both axioms hold exactly when the source energy is the
defect itself. In that case the source cone is the closed positive cone.

Fibre degrees do not establish Bézout: every source cone has nonnegative fibre degrees,
including cones whose boundary contains a negative-square cycle. The strict source cone has
the same obstruction, witnessed by a cycle strictly between the source and defect boundaries.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- Change the two fibre degrees while preserving the primitive source. -/
def withFibreDegrees (x : C) (a b : ℝ) : C :=
  x + (b - S.pair x S.V) • S.H + (a - S.pair x S.H) • S.V

theorem withFibreDegrees_pair_H (x : C) (a b : ℝ) :
    S.pair (S.withFibreDegrees x a b) S.H = a := by
  simp only [withFibreDegrees, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, S.pair_H_H, S.pair_V_H]
  ring

theorem withFibreDegrees_pair_V (x : C) (a b : ℝ) :
    S.pair (S.withFibreDegrees x a b) S.V = b := by
  simp only [withFibreDegrees, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, S.pair_H_V, S.pair_V_V]
  ring

theorem prim_withFibreDegrees (x : C) (a b : ℝ) :
    S.prim (S.withFibreDegrees x a b) = S.prim x := by
  rw [prim, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
  simp only [withFibreDegrees, prim]
  module

theorem defect_withFibreDegrees (x y : C) (a b c d : ℝ) :
    S.defect (S.withFibreDegrees x a b) (S.withFibreDegrees y c d) = S.defect x y := by
  rw [← S.defect_prim, S.prim_withFibreDegrees, S.prim_withFibreDegrees, S.defect_prim]

theorem pair_withFibreDegrees (x y : C) (a b c d : ℝ) :
    S.pair (S.withFibreDegrees x a b) (S.withFibreDegrees y c d) =
      a * d + b * c - S.defect x y := by
  have h := S.defect_withFibreDegrees x y a b c d
  rw [defect, polar, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
    S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V] at h
  linarith only [h]

theorem source_withFibreDegrees {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (x : C) (a b : ℝ) : Φ (S.withFibreDegrees x a b) = Φ x :=
  hfib x _ _

/-- Every nonnegative source energy is attained exactly as a polar capacity on its fibre. -/
theorem sourceCone_boundary {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (x : C) (hx : 0 ≤ Φ x) :
    S.withFibreDegrees x (Φ x) (1 / 2) ∈ S.sourceCone Φ ∧
      S.pair (S.withFibreDegrees x (Φ x) (1 / 2))
        (S.withFibreDegrees x (Φ x) (1 / 2)) = Φ x - S.defect x x := by
  have hpol : S.polar (S.withFibreDegrees x (Φ x) (1 / 2))
      (S.withFibreDegrees x (Φ x) (1 / 2)) = Φ x := by
    rw [S.polar_self, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
    ring
  constructor
  · rw [S.mem_sourceCone_iff, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
      S.source_withFibreDegrees hfib, hpol]
    exact ⟨hx, by positivity, le_rfl⟩
  · have hd := S.defect_withFibreDegrees x x (Φ x) (1 / 2) (Φ x) (1 / 2)
    rw [defect, hpol] at hd
    linarith only [hd]

/-- Bézout on a source cone forces an upper bound on the defect, opposite to the RR bound. -/
theorem defect_le_source_of_sourceCone_bezout {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (hB : S.BezoutAxiom (S.sourceCone Φ)) : ∀ x : C, S.defect x x ≤ Φ x := by
  intro x
  obtain ⟨hy, heq⟩ := S.sourceCone_boundary hfib x (hnn x)
  have h := hB _ hy _ hy
  rw [heq] at h
  linarith only [h]

/-- A strict gap in the RR floor produces a negative-square cycle in the strict source cone. -/
theorem exists_strictSourceCone_negative_square {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (x : C) (hnn : 0 ≤ Φ x) (hlt : Φ x < S.defect x x) :
    ∃ y ∈ S.strictSourceCone Φ, S.pair y y < 0 := by
  let m : ℝ := (Φ x + S.defect x x) / 2
  have hm : 0 < m := by dsimp [m]; linarith only [hnn, hlt]
  have hΦm : Φ x < m := by dsimp [m]; linarith only [hlt]
  have hmδ : m < S.defect x x := by dsimp [m]; linarith only [hlt]
  refine ⟨S.withFibreDegrees x m (1 / 2), ?_, ?_⟩
  · rw [S.mem_strictSourceCone_iff, S.withFibreDegrees_pair_H,
      S.withFibreDegrees_pair_V, S.source_withFibreDegrees hfib,
      S.polar_self, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
    refine ⟨hm, by positivity, ?_⟩
    linarith only [hΦm]
  · have hd := S.defect_withFibreDegrees x x m (1 / 2) m (1 / 2)
    rw [S.defect_self, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V] at hd
    linarith only [hd, hmδ]

theorem defect_le_source_of_strictSourceCone_bezout {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (hB : S.BezoutAxiom (S.strictSourceCone Φ)) : ∀ x : C, S.defect x x ≤ Φ x := by
  intro x
  by_contra h
  obtain ⟨y, hy, hyy⟩ := S.exists_strictSourceCone_negative_square hfib x (hnn x) (lt_of_not_ge h)
  exact (not_lt_of_ge (hB y hy y hy)) hyy

/-- Both geometric axioms force exact source representation, not merely a coercive floor. -/
theorem sourceCone_riemannRoch_and_bezout_iff {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.sourceCone Φ) ∧ S.BezoutAxiom (S.sourceCone Φ)) ↔
      ∀ x : C, Φ x = S.defect x x := by
  constructor
  · rintro ⟨hRR, hB⟩ x
    exact le_antisymm ((S.sourceCone_riemannRoch_iff_le_defect hnn heven hfib).mp hRR x)
      (S.defect_le_source_of_sourceCone_bezout hnn hfib hB x)
  · intro heq
    have hH : S.HodgeIndex := S.hodgeIndex_iff_defect_nonneg.mpr fun x => by
      rw [← heq x]
      exact hnn x
    exact ⟨S.sourceCone_riemannRoch_of_le_defect heven hnn (fun x => (heq x).le),
      S.sourceCone_bezout_of_defect_le hH (fun x => (heq x).ge)⟩

theorem strictSourceCone_riemannRoch_and_bezout_iff {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.strictSourceCone Φ) ∧ S.BezoutAxiom (S.strictSourceCone Φ)) ↔
      ∀ x : C, Φ x = S.defect x x := by
  constructor
  · rintro ⟨hRR, hB⟩ x
    have hRR' : S.RiemannRochAxiom (S.sourceCone Φ) := by
      intro y hy
      rcases hRR y hy with h | h
      · exact Or.inl (S.strictSourceCone_subset_sourceCone Φ h)
      · exact Or.inr (S.strictSourceCone_subset_sourceCone Φ h)
    exact le_antisymm ((S.sourceCone_riemannRoch_iff_le_defect hnn heven hfib).mp hRR' x)
      (S.defect_le_source_of_strictSourceCone_bezout hnn hfib hB x)
  · intro heq
    have hH : S.HodgeIndex := S.hodgeIndex_iff_defect_nonneg.mpr fun x => by
      rw [← heq x]
      exact hnn x
    exact ⟨S.strictSourceCone_riemannRoch_of_le_defect heven hnn (fun x => (heq x).le),
      S.strictSourceCone_bezout_of_defect_le hH (fun x => (heq x).ge)⟩

/-- The graded cone of the exact defect is the positive cone, even without Hodge index. -/
theorem gradedSourceCone_defect_eq_positiveCone :
    S.gradedSourceCone (fun x => S.defect x x) = S.positiveCone := by
  ext x
  change (0 ≤ S.pair x S.ample ∧ S.polar x x - S.pair x x ≤ S.polar x x) ↔
    (0 ≤ S.pair x x ∧ 0 ≤ S.pair x S.ample)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith only [h₁, h₂]

/-- Exact nonnegative source representation recovers the closed positive cone as a set. -/
theorem sourceCone_eq_positiveCone_of_exact_source {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heq : ∀ x : C, Φ x = S.defect x x) :
    S.sourceCone Φ = S.positiveCone := by
  rw [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn,
    show Φ = (fun x => S.defect x x) from funext heq, S.gradedSourceCone_defect_eq_positiveCone]

/-- Bézout is exactly a bound on every mixed source defect, without a Hodge-index premise. -/
theorem sourceCone_bezout_iff_defect_sq_le {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (S.sourceCone Φ) ↔
      ∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y := by
  constructor
  · intro hB x y
    let p := Real.sqrt (Φ x / 2)
    let q := Real.sqrt (Φ y / 2)
    have hp : 0 ≤ p := Real.sqrt_nonneg _
    have hq : 0 ≤ q := Real.sqrt_nonneg _
    have hp2 : p ^ 2 = Φ x / 2 := Real.sq_sqrt (div_nonneg (hnn x) (by positivity))
    have hq2 : q ^ 2 = Φ y / 2 := Real.sq_sqrt (div_nonneg (hnn y) (by positivity))
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
    have hny : S.withFibreDegrees (-y) q q ∈ S.sourceCone Φ := by
      rw [S.mem_sourceCone_iff, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
        S.source_withFibreDegrees hfib, heven, S.polar_self,
        S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
      exact ⟨hq, hq, by nlinarith only [hq2]⟩
    have hplus := hB _ hx _ hy
    have hminus := hB _ hx _ hny
    rw [S.pair_withFibreDegrees] at hplus hminus
    have hneg : S.defect x (-y) = -S.defect x y := by
      simp only [defect, polar, map_neg, LinearMap.neg_apply]
      ring
    rw [hneg] at hminus
    have hsq : (p * q + p * q) ^ 2 = Φ x * Φ y := by
      calc (p * q + p * q) ^ 2 = 4 * p ^ 2 * q ^ 2 := by ring
        _ = Φ x * Φ y := by rw [hp2, hq2]; ring
    nlinarith only [mul_nonneg hplus hminus, hsq]
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
    have hbound : S.defect x y ^ 2 ≤ S.polar x y ^ 2 :=
      (hcs x y).trans ((mul_le_mul hxΦ hyΦ (hnn y) hpx).trans hpolar)
    by_contra hpair
    have hlt : S.polar x y < S.defect x y := by
      dsimp only [defect]
      linarith only [lt_of_not_ge hpair]
    have hsum : 0 < S.defect x y + S.polar x y := by linarith only [hlt, hpxy]
    nlinarith only [hbound, mul_pos (sub_pos.mpr hlt) hsum]

/-- Nonnegative degree against every nonnegative fibre combination is automatic on a source cone. -/
theorem sourceCone_nonneg_fibre_degrees {Φ : C → ℝ} {x : C}
    (hx : x ∈ S.sourceCone Φ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ S.pair x (a • S.H + b • S.V) := by
  obtain ⟨hH, hV, -⟩ := (S.mem_sourceCone_iff Φ x).mp hx
  simpa only [map_add, map_smul, smul_eq_mul] using
    add_nonneg (mul_nonneg ha hH) (mul_nonneg hb hV)

/-- Under Hodge index, the upper source bound is also sufficient for Bézout. -/
theorem sourceCone_bezout_iff_defect_le_of_hodgeIndex {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (hH : S.HodgeIndex) :
    S.BezoutAxiom (S.sourceCone Φ) ↔ ∀ x : C, S.defect x x ≤ Φ x :=
  ⟨S.defect_le_source_of_sourceCone_bezout hnn hfib, S.sourceCone_bezout_of_defect_le hH⟩

/-- Fibre-degree positivity alone has Bézout exactly when the entire primitive defect vanishes. -/
theorem sourceCone_zero_bezout_iff :
    S.BezoutAxiom (S.sourceCone (fun _ => 0)) ↔ ∀ x : C, S.defect x x = 0 := by
  constructor
  · intro hB x
    have hp : S.prim x ∈ S.sourceCone (fun _ => 0) := by
      rw [S.mem_sourceCone_iff, S.pair_prim_H, S.pair_prim_V, S.polar_self,
        S.pair_prim_H, S.pair_prim_V]
      exact ⟨le_rfl, le_rfl, by ring_nf; exact le_rfl⟩
    have hnp : -S.prim x ∈ S.sourceCone (fun _ => 0) := by
      rw [S.mem_sourceCone_iff, S.polar_self]
      simp only [map_neg, LinearMap.neg_apply, S.pair_prim_H, S.pair_prim_V,
        neg_zero, mul_zero, zero_mul]
      exact ⟨le_rfl, le_rfl, le_rfl⟩
    have hlo := hB _ hp _ hp
    have hhi := hB _ hp _ hnp
    rw [S.pair_prim_prim] at hlo
    rw [map_neg, S.pair_prim_prim, neg_neg] at hhi
    exact le_antisymm (by linarith only [hlo]) hhi
  · intro heq
    apply S.sourceCone_bezout_of_defect_le
    · exact S.hodgeIndex_iff_defect_nonneg.mpr fun x => (heq x).ge
    · exact fun x => (heq x).le

end PolarSurface

open MeasureTheory

/-- An `L²` source cone has both axioms exactly when the Weil form equals that scalar `L²` form. -/
theorem l2SourceCone_riemannRoch_and_bezout_iff {c : ℝ} (hc : 0 ≤ c)
    (V : Submodule ℝ realTests) :
    ((scalingSubsurface V).RiemannRochAxiom (l2SourceCone c V) ∧
      (scalingSubsurface V).BezoutAxiom (l2SourceCone c V)) ↔
      ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 = weilPair f.1.1 f.1.1 := by
  rw [l2SourceCone,
    (scalingSubsurface V).sourceCone_riemannRoch_and_bezout_iff
      (l2SourceEnergy_nonneg hc V) (l2SourceEnergy_neg c V) (l2SourceEnergy_add_fibres c V)]
  simp only [l2SourceEnergy, scalingSubsurface_defect_self]
  exact ⟨fun h f => h (0, 0, f), fun h x => h x.2.2⟩

theorem strictL2SourceCone_riemannRoch_and_bezout_iff {c : ℝ} (hc : 0 ≤ c)
    (V : Submodule ℝ realTests) :
    ((scalingSubsurface V).RiemannRochAxiom (strictL2SourceCone c V) ∧
      (scalingSubsurface V).BezoutAxiom (strictL2SourceCone c V)) ↔
      ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 = weilPair f.1.1 f.1.1 := by
  rw [strictL2SourceCone,
    (scalingSubsurface V).strictSourceCone_riemannRoch_and_bezout_iff
      (l2SourceEnergy_nonneg hc V) (l2SourceEnergy_neg c V) (l2SourceEnergy_add_fibres c V)]
  simp only [l2SourceEnergy, scalingSubsurface_defect_self]
  exact ⟨fun h f => h (0, 0, f), fun h x => h x.2.2⟩

/-- Any strict slack in an `L²` lower bound gives an effective cycle with negative square. -/
theorem exists_strictL2SourceCone_negative_square {c : ℝ} (hc : 0 ≤ c)
    (V : Submodule ℝ realTests) (f : V)
    (hlt : c * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1) :
    ∃ x ∈ strictL2SourceCone c V, (scalingSubsurface V).pair x x < 0 := by
  exact (scalingSubsurface V).exists_strictSourceCone_negative_square
    (l2SourceEnergy_add_fibres c V) (0, 0, f) (l2SourceEnergy_nonneg hc V _) (by
      simpa only [l2SourceEnergy, scalingSubsurface_defect_self] using hlt)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
