import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFloquetDichotomy

/-!
# The stable class is inhabited

A criterion decides nothing until something satisfies it. A constant background is periodic with every
period, so the autonomous theory supplies the first inhabitants of the stability criterion, and with
explicit constants.

For the free field the monodromy is an isometry — the propagator conserves the energy exactly — so
`‖M‖ ≤ 1` and the clock keeps running by statement 313. For a small self-adjoint potential the
conserved energy differs from the state norm by a fixed factor, so the powers of the monodromy obey

`‖Mⁿ‖ ≤ √((1+b)/(1−b))`,

uniformly in `n`: the criterion of statement 310 is met, with a constant read off from the potential's
strength alone.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## A constant background -/

/-- A constant background is periodic with every period. -/
theorem periodic_const (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (T : ℝ) : ∀ r : ℝ, (fun _ : ℝ => W₀) (r + T) = (fun _ : ℝ => W₀) r := fun _ => rfl

theorem kgFieldGradT_const (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGradT (fun _ : ℝ => W₀) g h t = kgFieldGrad W₀ g h t := rfl

theorem kgFieldVelT_const (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVelT (fun _ : ℝ => W₀) g h t = kgFieldVel W₀ g h t := rfl

theorem kgFieldStateT_const (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT (fun _ : ℝ => W₀) g h t = kgFieldState W₀ g h t := rfl

/-- The energy norm of a datum is the square root of its energy. -/
theorem norm_kgPair_sq (g h : Lp ℂ 2 (volume : Measure E)) :
    ‖kgPair E (g, h)‖ ^ (2 : ℕ) = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := by
  rw [← kgEnergy_eq_norm_sq, kgEnergy, kgPair_fst, kgPair_snd]

/-! ## The free clock -/

section Free

variable {T : ℝ}

/-- **The free monodromy is an isometry.** -/
theorem norm_kgMonodromy_zero_apply (hT : ℝ) (v : KGEnergy E) :
    ‖kgPeriodMap (E := E) (fun _ : ℝ => 0) hT v‖ = ‖v‖ := by
  have hsq : ‖kgFieldGrad (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        v.fst v.snd hT‖ ^ (2 : ℕ)
      + ‖kgFieldVel (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        v.fst v.snd hT‖ ^ (2 : ℕ)
      = ‖v.fst‖ ^ (2 : ℕ) + ‖v.snd‖ ^ (2 : ℕ) := kgFieldEnergy_zero_op v.fst v.snd hT
  have hL : ‖kgPeriodMap (E := E) (fun _ : ℝ => 0) hT v‖ ^ (2 : ℕ) = ‖v.fst‖ ^ (2 : ℕ) + ‖v.snd‖ ^ (2 : ℕ) := by
    rw [kgPeriodMap, kgFieldStateT_const, ← kgFieldEnergy_eq_norm_sq]
    exact hsq
  have hR : ‖v‖ ^ (2 : ℕ) = ‖v.fst‖ ^ (2 : ℕ) + ‖v.snd‖ ^ (2 : ℕ) := by
    rw [← kgPair_fst_snd v, norm_kgPair_sq, kgPair_fst, kgPair_snd]
  have h1 : (0 : ℝ) ≤ ‖kgPeriodMap (E := E) (fun _ : ℝ => 0) hT v‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [hL, hR, h1, h2]

/-- **The free clock keeps running.** Its monodromy is a contraction over every period. -/
theorem norm_kgMonodromy_zero_le_one (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) :
    ‖kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul, kgMonodromy_apply]
    exact le_of_eq (norm_kgMonodromy_zero_apply T v)

end Free

/-! ## A small self-adjoint potential -/

section SmallPotential

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b T : ℝ}

/-- **A small real potential gives a uniformly bounded state**, in energy-space form. -/
theorem norm_kgFieldState_le_uniform (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldState W₀ g h t‖ ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖ := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hK0 : (0 : ℝ) ≤ (1 + b) / (1 - b) := by positivity
  have hen := kgFieldEnergy_uniform hb0 hb1 hW hsa g h t
  have hL : ‖kgFieldState W₀ g h t‖ ^ (2 : ℕ)
      = ‖kgFieldGrad W₀ g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W₀ g h t‖ ^ (2 : ℕ) :=
    (kgFieldEnergy_eq_norm_sq W₀ g h t).symm
  have hR : ‖kgPair E (g, h)‖ ^ (2 : ℕ) = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := norm_kgPair_sq g h
  have hsq : ‖kgFieldState W₀ g h t‖ ^ (2 : ℕ)
      ≤ (Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖) ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hK0, hL, hR]
    exact hen
  have h1 : (0 : ℝ) ≤ ‖kgFieldState W₀ g h t‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖ := by positivity
  nlinarith [hsq, h1, h2]

/-- **The monodromy of a small real potential has uniformly bounded powers**, with an explicit
constant: the stability criterion of statement 310 is met, and the class it describes is not
empty. -/
theorem norm_kgMonodromy_pow_le_of_small (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    (n : ℕ) :
    ‖kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T ^ n‖ ≤ Real.sqrt ((1 + b) / (1 - b)) := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hK0 : (0 : ℝ) ≤ Real.sqrt ((1 + b) / (1 - b)) := Real.sqrt_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun v => ?_
  have hval : (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T ^ n) v
      = kgFieldState W₀ v.fst v.snd ((n : ℝ) * T) := by
    have hpow := kgFieldStateT_monodromy_pow (T := T) hb0 hWb hWs (periodic_const W₀ T)
      v.fst v.snd n
    rw [kgPair_fst_snd] at hpow
    rw [← hpow, kgFieldStateT_const]
  rw [hval]
  have hle := norm_kgFieldState_le_uniform hb0 hb1 hW hsa v.fst v.snd ((n : ℝ) * T)
  rwa [kgPair_fst_snd] at hle

/-- **A clock in a small real potential is stable at every time.** -/
theorem norm_kgFieldState_le_of_small (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad W₀ g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W₀ g h t‖ ^ (2 : ℕ)
      ≤ (1 + b) / (1 - b) * (‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ)) :=
  kgFieldEnergy_uniform hb0 hb1 hW hsa g h t

end SmallPotential

end GaloisForLFunctions.HTGeometry
