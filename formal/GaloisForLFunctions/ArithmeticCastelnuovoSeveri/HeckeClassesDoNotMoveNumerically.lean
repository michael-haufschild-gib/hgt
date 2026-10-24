import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.NumericalEquivalenceOnTheScalingSurface

/-!
# Scaling and Hecke motion are not principal numerical equivalence

A compact source cannot be an eigenfunction of a nonzero translation. Scaling eigenvectors
therefore lie in the fibre plane. Nontrivial normalized Adams operations have zero fixed space;
the unnormalized Hecke operator fixes exactly the vertical fibre line. Nondegeneracy of the
scaling intersection form makes these also the exact numerically fixed spaces.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Every scaling eigenvector at nonzero logarithmic scale lies in the explicit fibre plane. -/
theorem scalingAction_eigen_iff {t : ℝ} (ht : t ≠ 0) (c : ℝ) (x : ScalingCycle) :
    scalingAction t x = c • x ↔ x.2.2 = 0 ∧
      (Real.exp (t / 2) - c) * x.1 = 0 ∧
      (Real.exp (-t / 2) - c) * x.2.1 = 0 := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ :=
      GaloisForLFunctions.ArithmeticIncidencePositivity.exists_radius_of_hasCompactSupport x.2.2.2.2
    have hshift : ∀ u : ℝ, x.2.2.1 u = c * x.2.2.1 (u + t) := by
      intro u
      have hu := congrArg (fun z : ScalingCycle => z.2.2.1 (u + t)) h
      change x.2.2.1 (u + t - t) = c * x.2.2.1 (u + t) at hu
      rw [show u + t - t = u by ring] at hu
      exact hu
    have hf : x.2.2 = 0 := Subtype.ext
      (GaloisForLFunctions.ArithmeticIncidencePositivity.eq_zero_of_eq_const_mul_shift ht hr hshift)
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

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
