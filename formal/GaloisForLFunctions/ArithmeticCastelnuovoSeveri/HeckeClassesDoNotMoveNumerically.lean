import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.NumericalEquivalenceOnTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochAwayFromTheLowFrequencyDivisor

/-!
# Scaling and Hecke motion are not principal numerical equivalence

A compact source cannot be an eigenfunction of a nonzero translation. Scaling eigenvectors
therefore lie in the fibre plane. Nontrivial normalized Adams operations have zero fixed space;
the unnormalized Hecke operator fixes exactly the vertical fibre line. Nondegeneracy of the
scaling intersection form makes these also the exact numerically fixed spaces.
Distinct scaling motions of a nonzero compact source are linearly independent, so no finite
Adams or Hecke combination supplies a nontrivial principal numerical relation either.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Every scaling eigenvector at nonzero logarithmic scale lies in the explicit fibre plane. -/
theorem scalingAction_eigen_iff {t : ℝ} (ht : t ≠ 0) (c : ℝ) (x : ScalingCycle) :
    scalingAction t x = c • x ↔ x.2.2 = 0 ∧
      (Real.exp (t / 2) - c) * x.1 = 0 ∧
      (Real.exp (-t / 2) - c) * x.2.1 = 0 := by
  constructor
  · intro h
    have hf : x.2.2 = 0 := by
      by_contra hne
      have hfun : x.2.2.1 ≠ 0 := fun hz => hne (Subtype.ext hz)
      let s : Fin 2 → ℝ := fun i => if i = 0 then 0 else t
      have hs : Function.Injective s := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [s, Ne.symm ht]
      have hli := linearIndependent_real_translate (g := x.2.2.1) hs x.2.2.2.2 hfun
      let a : Fin 2 → ℝ := fun i => if i = 0 then c else -1
      have hrel : ∑ i : Fin 2, a i • (fun u : ℝ => x.2.2.1 (u - s i)) = 0 := by
        rw [Fin.sum_univ_two]
        funext u
        have hu := congrArg (fun z : ScalingCycle => z.2.2.1 u) h
        change x.2.2.1 (u - t) = c * x.2.2.1 u at hu
        change c * x.2.2.1 (u - 0) + (-1) * x.2.2.1 (u - t) = 0
        rw [sub_zero, hu]
        ring
      have ha := (Fintype.linearIndependent_iff.mp hli) a hrel 1
      change (-1 : ℝ) = 0 at ha
      norm_num at ha
    have ha := congrArg Prod.fst h
    have hb := congrArg (fun z : ScalingCycle => z.2.1) h
    change Real.exp (t / 2) * x.1 = c * x.1 at ha
    change Real.exp (-t / 2) * x.2.1 = c * x.2.1 at hb
    exact ⟨hf, by nlinarith only [ha], by nlinarith only [hb]⟩
  · rintro ⟨hf, ha, hb⟩
    apply Prod.ext
    · change Real.exp (t / 2) * x.1 = c * x.1
      nlinarith only [ha]
    · apply Prod.ext
      · change Real.exp (-t / 2) * x.2.1 = c * x.2.1
        nlinarith only [hb]
      · apply Subtype.ext
        funext u
        change x.2.2.1 (u - t) = c * x.2.2.1 u
        rw [hf]
        simp only [Submodule.coe_zero, Pi.zero_apply, mul_zero]

/-- A nontrivial scaling action fixes only the zero compact scaling cycle. -/
theorem scalingAction_fixed_iff {t : ℝ} (ht : t ≠ 0) (x : ScalingCycle) :
    scalingAction t x = x ↔ x = 0 := by
  constructor
  · intro h
    have he : scalingAction t x = (1 : ℝ) • x := by rw [one_smul]; exact h
    obtain ⟨hf, ha, hb⟩ := (scalingAction_eigen_iff ht 1 x).mp he
    have hea : Real.exp (t / 2) - 1 ≠ 0 := by
      intro hz
      have hz' := (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp hz)
      exact ht (by linarith only [hz'])
    have heb : Real.exp (-t / 2) - 1 ≠ 0 := by
      intro hz
      have hz' := (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp hz)
      exact ht (by linarith only [hz'])
    exact Prod.ext ((mul_eq_zero.mp ha).resolve_left hea)
      (Prod.ext ((mul_eq_zero.mp hb).resolve_left heb) hf)
  · rintro rfl
    exact map_zero _

private theorem log_ne_zero_of_pos_ne_one {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) :
    Real.log q ≠ 0 := by
  intro h
  have he := Real.exp_log hq
  rw [h, Real.exp_zero] at he
  exact hq1 he.symm

/-- A nonidentity positive Adams scale has no nonzero fixed compact class. -/
theorem adamsOp_fixed_iff {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) (x : ScalingCycle) :
    adamsOp q x = x ↔ x = 0 :=
  scalingAction_fixed_iff (log_ne_zero_of_pos_ne_one hq hq1) x

/-- The vertical fibre line is exactly the fixed space of a nonidentity positive Hecke operator. -/
theorem heckeCorrespondence_fixed_iff {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (x : ScalingCycle) :
    heckeCorrespondence q x = x ↔ ∃ b : ℝ, x = b • scalingSurface.V := by
  constructor
  · intro h
    have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    have he : adamsOp q x = (Real.sqrt q)⁻¹ • x := by
      have hh := congrArg (fun y : ScalingCycle => (Real.sqrt q)⁻¹ • y) h
      simpa only [heckeCorrespondence, LinearMap.smul_apply, smul_smul,
        inv_mul_cancel₀ hs, one_smul] using hh
    have hf := ((scalingAction_eigen_iff (log_ne_zero_of_pos_ne_one hq hq1)
      ((Real.sqrt q)⁻¹) x).mp he).1
    have hp := congrArg (fun y => scalingSurface.pair y scalingSurface.V) h
    rw [pair_heckeCorrespondence_V hq, scalingSurface_pair_V, hf,
      Submodule.coe_zero, poleA_zero, add_zero] at hp
    have hqa : (q - 1) * x.1 = 0 := by nlinarith only [hp]
    have ha : x.1 = 0 := (mul_eq_zero.mp hqa).resolve_left
      (fun hz => hq1 (sub_eq_zero.mp hz))
    refine ⟨x.2.1, ?_⟩
    apply Prod.ext
    · change x.1 = x.2.1 * 0
      rw [ha, mul_zero]
    · apply Prod.ext
      · change x.2.1 = x.2.1 * 1
        rw [mul_one]
      · change x.2.2 = x.2.1 • (0 : realTests)
        rw [hf, smul_zero]
  · rintro ⟨b, rfl⟩
    rw [map_smul, heckeCorrespondence_V hq]

/-- Numerically fixed Adams classes are zero, without an RH premise. -/
theorem adamsOp_numerically_fixed_iff {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (x : ScalingCycle) :
    (∀ y : ScalingCycle, scalingSurface.pair (adamsOp q x) y = scalingSurface.pair x y) ↔
      x = 0 := by
  rw [scalingSurface_numerical_equivalence_iff_eq, adamsOp_fixed_iff hq hq1]

/-- Numerically fixed Hecke classes are exactly the vertical fibre line. -/
theorem heckeCorrespondence_numerically_fixed_iff {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (x : ScalingCycle) :
    (∀ y : ScalingCycle, scalingSurface.pair (heckeCorrespondence q x) y = scalingSurface.pair x y) ↔
      ∃ b : ℝ, x = b • scalingSurface.V := by
  rw [scalingSurface_numerical_equivalence_iff_eq, heckeCorrespondence_fixed_iff hq hq1]

private def compactSourceProjection : ScalingCycle →ₗ[ℝ] (ℝ → ℝ) where
  toFun x := x.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every finite distinct-scale orbit of a class with nonzero compact source is free. -/
theorem scalingAction_orbit_linearIndependent {N : ℕ} {t : Fin N → ℝ}
    (ht : Function.Injective t) (x : ScalingCycle) (hx : x.2.2 ≠ 0) :
    LinearIndependent ℝ (fun i => scalingAction (t i) x) := by
  have hsource : x.2.2.1 ≠ 0 := fun h => hx (Subtype.ext h)
  have hli := linearIndependent_real_translate (g := x.2.2.1) ht x.2.2.2.2 hsource
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hproj (i : Fin N) :
      compactSourceProjection (scalingAction (t i) x) = fun u => x.2.2.1 (u - t i) := rfl
  have hs := congrArg compactSourceProjection hc
  simp only [map_sum, map_smul, map_zero, hproj] at hs
  exact (Fintype.linearIndependent_iff.mp hli) c hs

/-- A nonzero compact source admits no finite numerical relation among distinct scaling motions. -/
theorem scalingAction_sum_numerically_trivial_iff {N : ℕ} {t : Fin N → ℝ}
    (ht : Function.Injective t) (x : ScalingCycle) (hx : x.2.2 ≠ 0) (c : Fin N → ℝ) :
    (∀ y : ScalingCycle,
      scalingSurface.pair (∑ i, c i • scalingAction (t i) x) y = 0) ↔ ∀ i, c i = 0 := by
  rw [scalingSurface_pairing_nondegenerate]
  constructor
  · exact (Fintype.linearIndependent_iff.mp (scalingAction_orbit_linearIndependent ht x hx)) c
  · intro hc
    simp only [hc, zero_smul, Finset.sum_const_zero]

/-- Distinct positive Adams scales are linearly independent on every nonzero compact source. -/
theorem adamsOp_orbit_linearIndependent {N : ℕ} {q : Fin N → ℝ}
    (hq : ∀ i, 0 < q i) (hqi : Function.Injective q)
    (x : ScalingCycle) (hx : x.2.2 ≠ 0) :
    LinearIndependent ℝ (fun i => adamsOp (q i) x) := by
  apply scalingAction_orbit_linearIndependent (x := x) (hx := hx)
  intro i j hij
  apply hqi
  exact (Real.exp_log (hq i)).symm.trans ((congrArg Real.exp hij).trans (Real.exp_log (hq j)))

/-- Unnormalized Hecke scales retain the same finite orbit freedom. -/
theorem heckeCorrespondence_orbit_linearIndependent {N : ℕ} {q : Fin N → ℝ}
    (hq : ∀ i, 0 < q i) (hqi : Function.Injective q)
    (x : ScalingCycle) (hx : x.2.2 ≠ 0) :
    LinearIndependent ℝ (fun i => heckeCorrespondence (q i) x) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [heckeCorrespondence, LinearMap.smul_apply, smul_smul] at hc
  have hh := (Fintype.linearIndependent_iff.mp (adamsOp_orbit_linearIndependent hq hqi x hx))
    (fun i => c i * Real.sqrt (q i)) hc
  intro i
  exact (mul_eq_zero.mp (hh i)).resolve_right (Real.sqrt_pos.mpr (hq i)).ne'

/-- No nonzero finite Hecke combination of a nonzero compact source is a principal numerical relation. -/
theorem heckeCorrespondence_sum_numerically_trivial_iff {N : ℕ} {q : Fin N → ℝ}
    (hq : ∀ i, 0 < q i) (hqi : Function.Injective q)
    (x : ScalingCycle) (hx : x.2.2 ≠ 0) (c : Fin N → ℝ) :
    (∀ y : ScalingCycle,
      scalingSurface.pair (∑ i, c i • heckeCorrespondence (q i) x) y = 0) ↔ ∀ i, c i = 0 := by
  rw [scalingSurface_pairing_nondegenerate]
  constructor
  · exact (Fintype.linearIndependent_iff.mp
      (heckeCorrespondence_orbit_linearIndependent hq hqi x hx)) c
  · intro hc
    simp only [hc, zero_smul, Finset.sum_const_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
