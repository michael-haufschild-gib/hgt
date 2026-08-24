import GaloisForLFunctions.HTGeometry.CharacterStabilizerRank

/-!
# Rank of a unitary character stabilizer

The compact-torus stabilizer of an integer character set has the same rank
bound as its full complexification.  Real one-parameter subgroups detect real
and imaginary parts of every complex annihilator, so finite-dimensional
duality gives the result directly.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ}

/-- Unit-torus points annihilating every integer character in `A`. -/
def unitCharacterStabilizer (A : Set (Fin r → ℤ)) : Set (Fin r → ℂˣ) :=
  {u | (fun i => (u i : ℂ)) ∈ unitTorus (Fin r) ∧
    ∀ m ∈ A, ∏ i, ((u i : ℂ)) ^ (m i) = 1}

@[simp] theorem mem_unitCharacterStabilizer {A : Set (Fin r → ℤ)}
    {u : Fin r → ℂˣ} :
    u ∈ unitCharacterStabilizer A ↔
      (fun i => (u i : ℂ)) ∈ unitTorus (Fin r) ∧
        ∀ m ∈ A, ∏ i, ((u i : ℂ)) ^ (m i) = 1 := Iff.rfl

private theorem real_dot_eq_zero_of_unit_scaleAnnihilator
    {A : Set (Fin r → ℤ)} {a : Fin r → ℤ} {b : Fin r → ℝ}
    (hb : ∀ m ∈ A, ∑ i, b i * (m i : ℝ) = 0)
    (ha : a ∈ scaleAnnihilator ℂ (unitCharacterStabilizer A)) :
    ∑ i, b i * (a i : ℝ) = 0 := by
  classical
  by_contra hne
  let q : ℝ := ∑ i, b i * (a i : ℝ)
  let t : ℝ := Real.pi / q
  let u : Fin r → ℂˣ := fun i =>
    Units.mk0 (Complex.exp (((t * b i : ℝ) : ℂ) * Complex.I))
      (Complex.exp_ne_zero _)
  have hu : u ∈ unitCharacterStabilizer A := by
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [u, Units.val_mk0] using
        Complex.norm_exp_ofReal_mul_I (t * b i)
    · intro m hm
      change ∏ i, Complex.exp (((t * b i : ℝ) : ℂ) * Complex.I) ^ (m i) = 1
      simp_rw [← Complex.exp_int_mul]
      rw [← Complex.exp_sum]
      have hreal : ∑ i, (m i : ℝ) * (t * b i) = 0 := by
        calc
          ∑ i, (m i : ℝ) * (t * b i) =
              t * ∑ i, b i * (m i : ℝ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by ring
          _ = 0 := by rw [hb m hm, mul_zero]
      have hsum :
          ∑ i, (m i : ℂ) * (((t * b i : ℝ) : ℂ) * Complex.I) = 0 := by
        calc
          ∑ i, (m i : ℂ) * (((t * b i : ℝ) : ℂ) * Complex.I) =
              ((∑ i, (m i : ℝ) * (t * b i) : ℝ) : ℂ) * Complex.I := by
                have hcast :
                    ((↑(∑ i, (m i : ℝ) * (t * b i)) : ℂ)) =
                      ∑ i, (((m i : ℝ) * (t * b i) : ℝ) : ℂ) := by
                  push_cast
                  rfl
                rw [hcast, Finset.sum_mul]
                exact Finset.sum_congr rfl fun i _ => by
                  push_cast
                  ring
          _ = 0 := by rw [hreal]; simp
      rw [hsum, Complex.exp_zero]
  have hua := ha u hu
  have hprod :
      ∏ i, Complex.exp (((t * b i : ℝ) : ℂ) * Complex.I) ^ (a i) = 1 := by
    simpa only [u, Units.val_mk0] using hua
  simp_rw [← Complex.exp_int_mul] at hprod
  rw [← Complex.exp_sum] at hprod
  have hreal : ∑ i, (a i : ℝ) * (t * b i) = t * q := by
    change ∑ i, (a i : ℝ) * (t * b i) =
      t * ∑ i, b i * (a i : ℝ)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum :
      ∑ i, (a i : ℂ) * (((t * b i : ℝ) : ℂ) * Complex.I) =
        ((t * q : ℝ) : ℂ) * Complex.I := by
    calc
      ∑ i, (a i : ℂ) * (((t * b i : ℝ) : ℂ) * Complex.I) =
          ((∑ i, (a i : ℝ) * (t * b i) : ℝ) : ℂ) * Complex.I := by
            have hcast :
                ((↑(∑ i, (a i : ℝ) * (t * b i)) : ℂ)) =
                  ∑ i, (((a i : ℝ) * (t * b i) : ℝ) : ℂ) := by
              push_cast
              rfl
            rw [hcast, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by
              push_cast
              ring
      _ = ((t * q : ℝ) : ℂ) * Complex.I := by rw [hreal]
  rw [hsum] at hprod
  have htq : t * q = Real.pi := div_mul_cancel₀ Real.pi hne
  rw [htq, Complex.exp_pi_mul_I] at hprod
  norm_num at hprod

/-- The unitary double annihilator of an integer character set has no larger
rank than that character set. -/
theorem rank_scaleAnnihilator_unitCharacterStabilizer_le
    (A : Set (Fin r → ℤ)) :
    Module.rank ℚ
        (Submodule.span ℚ
          (intCharacterToRat '' scaleAnnihilator ℂ (unitCharacterStabilizer A))) ≤
      Module.rank ℤ (Submodule.span ℤ A) := by
  classical
  let T := scaleAnnihilator ℂ (unitCharacterStabilizer A)
  have hfin : Module.finrank ℂ
        (Submodule.span ℂ (intCharacterToComplex '' T)) ≤
      Module.finrank ℂ
        (Submodule.span ℂ (intCharacterToComplex '' A)) := by
    apply finrank_span_le_of_annihilator
    intro c hc _
    rintro ⟨a, ha, rfl⟩
    have hRe : ∑ i, (c i).re * (a i : ℝ) = 0 := by
      refine real_dot_eq_zero_of_unit_scaleAnnihilator
        (A := A) (a := a) (b := fun i => (c i).re) ?_ ha
      intro m hm
      have h := hc (intCharacterToComplex m) ⟨m, hm, rfl⟩
      have hre := congrArg Complex.re h
      simpa [intCharacterToComplex, Complex.mul_re] using hre
    have hIm : ∑ i, (c i).im * (a i : ℝ) = 0 := by
      refine real_dot_eq_zero_of_unit_scaleAnnihilator
        (A := A) (a := a) (b := fun i => (c i).im) ?_ ha
      intro m hm
      have h := hc (intCharacterToComplex m) ⟨m, hm, rfl⟩
      have him := congrArg Complex.im h
      simpa [intCharacterToComplex, Complex.mul_im] using him
    apply Complex.ext
    · simpa [intCharacterToComplex, Complex.mul_re] using hRe
    · simpa [intCharacterToComplex, Complex.mul_im] using hIm
  have hTmap : Module.rank ℤ (Submodule.span ℤ T) =
      Module.rank ℤ (Submodule.span ℤ (intCharacterToRat '' T)) := by
    rw [← Submodule.map_span]
    exact (Submodule.equivMapOfInjective _ injective_intCharacterToRat
      (Submodule.span ℤ T)).rank_eq
  rw [← rank_span_int_eq_rank_span_rat, ← hTmap,
    ← finrank_span_intCharacterToComplex T,
    ← finrank_span_intCharacterToComplex A]
  exact_mod_cast hfin

end

end GaloisForLFunctions.HTGeometry
