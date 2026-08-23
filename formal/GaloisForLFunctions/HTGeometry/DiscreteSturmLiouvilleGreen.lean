import GaloisForLFunctions.HTGeometry.DiscreteEnergyBootstrap

/-!
# A discrete Sturm--Liouville Liouville--Green bound

For the discrete Sturm--Liouville recurrence

`(ρ_{n+1} Δu_{n+1}) − (ρ_n Δu_n) + Q_{n+1} u_{n+1} = 0`

with positive slowly varying weight `ρ` and positive slowly varying potential `Q`, the energy

`E_n = (ρ_n Δu_n)² + ρ_n Q_n u_n u_{n+1}`

obeys the exact drift law

`E_{n+1} − E_n = Δ(ρQ)_n · u_n u_{n+1} + Q_{n+1} Δρ_n · u_{n+1} Δu_n`,

whose first term is cancelled to second order by dividing by `√(ρQ)` and whose second term is
already summable.  One discrete Abel summation of the virial identity

`(ρ_{n+1} Δu_{n+1})² − ρ_{n+1} Q_{n+1} u_{n+1}² = ρ_{n+1} Δ(u_{n+1} ρ_n Δu_n)_n`

then shows that `F_n = E_n / √(ρ_n Q_n)` stays bounded, whence
`u_n² ≤ 2 E_n / (ρ_n Q_n) ≲ 1/√(ρ_n Q_n)`: the Liouville--Green amplitude `(ρQ)^{-1/4}`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- The Sturm--Liouville flux `ρ_n Δu_n`. -/
def slgFlux (ρ u : ℕ → ℝ) (n : ℕ) : ℝ := ρ n * (u (n + 1) - u n)

/-- The Liouville--Green weight `ρ_n Q_n`. -/
def slgWeight (ρ Q : ℕ → ℝ) (n : ℕ) : ℝ := ρ n * Q n

/-- The discrete Sturm--Liouville recurrence. -/
def IsSLGSolution (ρ Q u : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, slgFlux ρ u (n + 1) - slgFlux ρ u n = -(Q (n + 1)) * u (n + 1)

/-- The Sturm--Liouville energy. -/
def slgEnergy (ρ Q u : ℕ → ℝ) (n : ℕ) : ℝ :=
  slgFlux ρ u n ^ 2 + slgWeight ρ Q n * (u n * u (n + 1))

/-- The Sturm--Liouville virial expression. -/
def slgVirial (ρ Q u : ℕ → ℝ) (n : ℕ) : ℝ :=
  slgFlux ρ u n ^ 2 - slgWeight ρ Q n * u n ^ 2

/-- The discrete primitive of the virial expression. -/
def slgPrimitive (ρ u : ℕ → ℝ) (n : ℕ) : ℝ := u (n + 1) * slgFlux ρ u n

variable {ρ Q u : ℕ → ℝ} {n : ℕ}

/-- **The exact energy drift law.** -/
theorem slgEnergy_succ_sub (h : IsSLGSolution ρ Q u) (n : ℕ) :
    slgEnergy ρ Q u (n + 1) - slgEnergy ρ Q u n
      = (slgWeight ρ Q (n + 1) - slgWeight ρ Q n) * (u n * u (n + 1))
        + Q (n + 1) * (ρ (n + 1) - ρ n) * (u (n + 1) * (u (n + 1) - u n)) := by
  have hr := h n
  simp only [slgFlux] at hr
  simp only [slgEnergy, slgWeight, slgFlux]
  linear_combination (ρ (n + 1) * (u (n + 1 + 1) - u (n + 1)) + ρ n * (u (n + 1) - u n)) * hr

/-- **The virial expression is an exact discrete derivative.** -/
theorem slgVirial_succ (h : IsSLGSolution ρ Q u) (n : ℕ) :
    slgVirial ρ Q u (n + 1)
      = ρ (n + 1) * (slgPrimitive ρ u (n + 1) - slgPrimitive ρ u n) := by
  have hr := h n
  simp only [slgFlux] at hr
  simp only [slgVirial, slgPrimitive, slgWeight, slgFlux]
  linear_combination (-(ρ (n + 1) * u (n + 1))) * hr

/-- **The virial splitting.** -/
theorem two_mul_sq_slgFlux_sub_energy (hρ : ρ n ≠ 0) :
    2 * slgFlux ρ u n ^ 2 - slgEnergy ρ Q u n
      = slgVirial ρ Q u n - Q n * (u n * slgFlux ρ u n) := by
  simp only [slgEnergy, slgVirial, slgWeight, slgFlux]
  field_simp
  ring

/-! ## Positivity -/

theorem slgEnergy_nonneg (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ 4 * ρ n) :
    0 ≤ slgEnergy ρ Q u n := by
  have hkey : 0 ≤ ρ n * slgEnergy ρ Q u n := by
    have hexp : ρ n * slgEnergy ρ Q u n
        = ρ n * slgFlux ρ u n ^ 2 + Q n * (ρ n * u n) ^ 2
          + Q n * (ρ n * u n) * slgFlux ρ u n := by
      simp only [slgEnergy, slgWeight, slgFlux]; ring
    rw [hexp]
    nlinarith [sq_nonneg (2 * ρ n * slgFlux ρ u n + Q n * (ρ n * u n)),
      mul_nonneg (mul_nonneg hQ (sq_nonneg (ρ n * u n))) (by linarith : (0:ℝ) ≤ 4 * ρ n - Q n),
      hρ]
  nlinarith [hkey, hρ]

theorem slgWeight_mul_sq_le (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ 2 * ρ n) :
    slgWeight ρ Q n * u n ^ 2 ≤ 2 * slgEnergy ρ Q u n := by
  have hkey : 0 ≤ ρ n * (2 * slgEnergy ρ Q u n - slgWeight ρ Q n * u n ^ 2) := by
    have hexp : ρ n * (2 * slgEnergy ρ Q u n - slgWeight ρ Q n * u n ^ 2)
        = 2 * ρ n * slgFlux ρ u n ^ 2 + Q n * (ρ n * u n) ^ 2
          + 2 * (Q n * (ρ n * u n) * slgFlux ρ u n) := by
      simp only [slgEnergy, slgWeight, slgFlux]; ring
    rw [hexp]
    nlinarith [sq_nonneg (4 * ρ n * slgFlux ρ u n + 2 * (Q n * (ρ n * u n))),
      mul_nonneg (mul_nonneg hQ (sq_nonneg (ρ n * u n))) (by linarith : (0:ℝ) ≤ 2 * ρ n - Q n),
      hρ]
  nlinarith [hkey, hρ]

theorem sq_slgFlux_le (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ 2 * ρ n) :
    slgFlux ρ u n ^ 2 ≤ 2 * slgEnergy ρ Q u n := by
  have hkey : 0 ≤ ρ n * (2 * slgEnergy ρ Q u n - slgFlux ρ u n ^ 2) := by
    have hexp : ρ n * (2 * slgEnergy ρ Q u n - slgFlux ρ u n ^ 2)
        = ρ n * slgFlux ρ u n ^ 2 + 2 * (Q n * (ρ n * u n) ^ 2)
          + 2 * (Q n * (ρ n * u n) * slgFlux ρ u n) := by
      simp only [slgEnergy, slgWeight, slgFlux]; ring
    rw [hexp]
    nlinarith [sq_nonneg (2 * ρ n * slgFlux ρ u n + 2 * (Q n * (ρ n * u n))),
      mul_nonneg (mul_nonneg hQ (sq_nonneg (ρ n * u n))) (by linarith : (0:ℝ) ≤ 2 * ρ n - Q n),
      hρ]
  nlinarith [hkey, hρ]

/-! ## The normalized energy -/

/-- The extra drift term produced by the variation of the weight `ρ`. -/
def slgExtra (ρ Q u : ℕ → ℝ) (n : ℕ) : ℝ :=
  Q (n + 1) * (ρ (n + 1) - ρ n) * (u (n + 1) * (u (n + 1) - u n))

theorem mul_slgExtra (ρ Q u : ℕ → ℝ) (n : ℕ) :
    ρ n * slgExtra ρ Q u n
      = Q (n + 1) * (ρ (n + 1) - ρ n) * slgPrimitive ρ u n := by
  simp only [slgExtra, slgPrimitive, slgFlux]
  ring

/-- The normalized energy `E / √(ρQ)`. -/
noncomputable def slgNormalizedEnergy (ρ Q u : ℕ → ℝ) (n : ℕ) : ℝ :=
  slgEnergy ρ Q u n / Real.sqrt (slgWeight ρ Q n)

/-- The Liouville--Green drift coefficient. -/
noncomputable def slgDrift (ρ Q : ℕ → ℝ) (n : ℕ) : ℝ :=
  (slgWeight ρ Q n - slgWeight ρ Q (n + 1))
    / (slgWeight ρ Q n * Real.sqrt (slgWeight ρ Q (n + 1)))

/-- The weight ratio appearing in the drift; it is `1/2` to leading order. -/
noncomputable def slgWeightRatio (ρ Q : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (slgWeight ρ Q (n + 1))
    / (Real.sqrt (slgWeight ρ Q n) + Real.sqrt (slgWeight ρ Q (n + 1)))

/-- The deviation of the weight ratio from `1/2`. -/
noncomputable def slgRatioDefect (ρ Q : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (slgWeight ρ Q n) - Real.sqrt (slgWeight ρ Q (n + 1)))
    / (2 * (Real.sqrt (slgWeight ρ Q n) + Real.sqrt (slgWeight ρ Q (n + 1))))

theorem slg_increment_algebra {sa sb d M G : ℝ} (hsa : 0 < sa) (hsb : 0 < sb) :
    ((d ^ 2 + sa ^ 2 * M) + (sb ^ 2 - sa ^ 2) * M + G) / sb - (d ^ 2 + sa ^ 2 * M) / sa
      = ((sa ^ 2 - sb ^ 2) / (sa ^ 2 * sb))
        * (d ^ 2 - (sb / (sa + sb)) * (d ^ 2 + sa ^ 2 * M)) + G / sb := by
  have hsum : sa + sb ≠ 0 := by positivity
  have hsa' : sa ≠ 0 := hsa.ne'
  have hsb' : sb ≠ 0 := hsb.ne'
  field_simp
  ring

/-- **The exact normalized-energy increment.** -/
theorem slgNormalizedEnergy_succ_sub (h : IsSLGSolution ρ Q u) {n : ℕ}
    (hW : 0 < slgWeight ρ Q n) (hW' : 0 < slgWeight ρ Q (n + 1)) :
    slgNormalizedEnergy ρ Q u (n + 1) - slgNormalizedEnergy ρ Q u n
      = slgDrift ρ Q n
          * (slgFlux ρ u n ^ 2 - slgWeightRatio ρ Q n * slgEnergy ρ Q u n)
        + slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1)) := by
  have hsa : 0 < Real.sqrt (slgWeight ρ Q n) := Real.sqrt_pos.mpr hW
  have hsb : 0 < Real.sqrt (slgWeight ρ Q (n + 1)) := Real.sqrt_pos.mpr hW'
  have hsa2 : Real.sqrt (slgWeight ρ Q n) ^ 2 = slgWeight ρ Q n := Real.sq_sqrt hW.le
  have hsb2 : Real.sqrt (slgWeight ρ Q (n + 1)) ^ 2 = slgWeight ρ Q (n + 1) :=
    Real.sq_sqrt hW'.le
  have key := slg_increment_algebra (d := slgFlux ρ u n) (M := u n * u (n + 1))
    (G := slgExtra ρ Q u n) hsa hsb
  rw [hsa2, hsb2] at key
  have hEn : slgEnergy ρ Q u n = slgFlux ρ u n ^ 2 + slgWeight ρ Q n * (u n * u (n + 1)) := rfl
  have hEsucc : slgEnergy ρ Q u (n + 1)
      = slgFlux ρ u n ^ 2 + slgWeight ρ Q n * (u n * u (n + 1))
        + (slgWeight ρ Q (n + 1) - slgWeight ρ Q n) * (u n * u (n + 1))
        + slgExtra ρ Q u n := by
    have := slgEnergy_succ_sub h n
    rw [hEn] at this
    simp only [slgExtra]
    linarith [this]
  rw [slgNormalizedEnergy, slgNormalizedEnergy, slgDrift, slgWeightRatio, hEsucc, hEn]
  exact key

theorem slgWeightRatio_eq (hW : 0 < slgWeight ρ Q n) (hW' : 0 < slgWeight ρ Q (n + 1)) :
    slgWeightRatio ρ Q n = 1 / 2 - slgRatioDefect ρ Q n := by
  have hsa : 0 < Real.sqrt (slgWeight ρ Q n) := Real.sqrt_pos.mpr hW
  have hsb : 0 < Real.sqrt (slgWeight ρ Q (n + 1)) := Real.sqrt_pos.mpr hW'
  have hsum : Real.sqrt (slgWeight ρ Q n) + Real.sqrt (slgWeight ρ Q (n + 1)) ≠ 0 := by positivity
  rw [slgWeightRatio, slgRatioDefect]
  field_simp
  ring

/-- **The normalized-energy increment split into a virial derivative, a small oscillating tail, a
second-order weight defect, and the weight-variation term.** -/
theorem slgNormalizedEnergy_succ_sub_split (h : IsSLGSolution ρ Q u) {n : ℕ}
    (hρ : 0 < ρ n) (hW : 0 < slgWeight ρ Q n) (hW' : 0 < slgWeight ρ Q (n + 1)) :
    slgNormalizedEnergy ρ Q u (n + 1) - slgNormalizedEnergy ρ Q u n
      = slgDrift ρ Q n * (slgVirial ρ Q u n / 2)
        - slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2)
        + slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n
        + slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1)) := by
  have hstep := slgNormalizedEnergy_succ_sub h hW hW'
  have hratio := slgWeightRatio_eq (ρ := ρ) (Q := Q) (n := n) hW hW'
  have hvir := two_mul_sq_slgFlux_sub_energy (ρ := ρ) (Q := Q) (u := u) (n := n) hρ.ne'
  rw [hstep, hratio]
  have hinner : slgFlux ρ u n ^ 2 - (1 / 2 - slgRatioDefect ρ Q n) * slgEnergy ρ Q u n
      = slgVirial ρ Q u n / 2 - Q n * (u n * slgFlux ρ u n) / 2
        + slgRatioDefect ρ Q n * slgEnergy ρ Q u n := by
    linarith [hvir]
  rw [hinner]
  ring

/-! ## Size bounds -/

theorem slgNormalizedEnergy_nonneg (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ 4 * ρ n) :
    0 ≤ slgNormalizedEnergy ρ Q u n :=
  div_nonneg (slgEnergy_nonneg hρ hQ hQρ) (Real.sqrt_nonneg _)

theorem slgEnergy_eq_normalized (hW : 0 < slgWeight ρ Q n) :
    slgEnergy ρ Q u n = slgNormalizedEnergy ρ Q u n * Real.sqrt (slgWeight ρ Q n) := by
  have hs : Real.sqrt (slgWeight ρ Q n) ≠ 0 := (Real.sqrt_pos.mpr hW).ne'
  rw [slgNormalizedEnergy]
  field_simp

theorem sqrt_slgWeight_le (hρ : 0 < ρ n) (_hQ : 0 ≤ Q n) (hQρ : Q n ≤ ρ n) :
    Real.sqrt (slgWeight ρ Q n) ≤ ρ n := by
  have hle : slgWeight ρ Q n ≤ ρ n ^ 2 := by
    simp only [slgWeight]
    nlinarith
  calc Real.sqrt (slgWeight ρ Q n) ≤ Real.sqrt (ρ n ^ 2) := Real.sqrt_le_sqrt hle
    _ = ρ n := Real.sqrt_sq hρ.le

/-- The mixed term is controlled by twice the normalized energy. -/
theorem abs_mul_slgFlux_le (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ 2 * ρ n)
    (hW : 0 < slgWeight ρ Q n) :
    |u n * slgFlux ρ u n| ≤ 2 * slgNormalizedEnergy ρ Q u n := by
  have hE := slgEnergy_nonneg (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith)
  have hF := slgNormalizedEnergy_nonneg (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith)
  have h1 := slgWeight_mul_sq_le (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ hQρ
  have h2 := sq_slgFlux_le (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ hQρ
  have hFsq : (2 * slgNormalizedEnergy ρ Q u n) ^ 2 * slgWeight ρ Q n
      = 4 * slgEnergy ρ Q u n ^ 2 := by
    rw [slgNormalizedEnergy, mul_pow, div_pow, Real.sq_sqrt hW.le]
    field_simp
    ring
  have hsq : (u n * slgFlux ρ u n) ^ 2 * slgWeight ρ Q n
      ≤ (2 * slgNormalizedEnergy ρ Q u n) ^ 2 * slgWeight ρ Q n := by
    rw [hFsq]
    have hvd : (u n * slgFlux ρ u n) ^ 2 * slgWeight ρ Q n
        = (slgWeight ρ Q n * u n ^ 2) * slgFlux ρ u n ^ 2 := by ring
    rw [hvd]
    nlinarith [h1, h2, sq_nonneg (slgFlux ρ u n), hE]
  have hsq' : (u n * slgFlux ρ u n) ^ 2 ≤ (2 * slgNormalizedEnergy ρ Q u n) ^ 2 :=
    le_of_mul_le_mul_right (by linarith [hsq]) hW
  have hs := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hs

/-- The virial primitive is controlled by four times the normalized energy. -/
theorem abs_slgPrimitive_le (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ ρ n)
    (hW : 0 < slgWeight ρ Q n) :
    |slgPrimitive ρ u n| ≤ 4 * slgNormalizedEnergy ρ Q u n := by
  have hE := slgEnergy_nonneg (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith)
  have hF := slgNormalizedEnergy_nonneg (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith)
  have hmix := abs_mul_slgFlux_le (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith) hW
  have hd := sq_slgFlux_le (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith)
  have hEF := slgEnergy_eq_normalized (ρ := ρ) (Q := Q) (u := u) (n := n) hW
  have hsw := sqrt_slgWeight_le (ρ := ρ) (Q := Q) (n := n) hρ hQ hQρ
  have hsplit : ρ n * slgPrimitive ρ u n
      = ρ n * (u n * slgFlux ρ u n) + slgFlux ρ u n ^ 2 := by
    simp only [slgPrimitive, slgFlux]
    ring
  have habs : |ρ n * slgPrimitive ρ u n| ≤ ρ n * (4 * slgNormalizedEnergy ρ Q u n) := by
    rw [hsplit]
    have hb1 : |ρ n * (u n * slgFlux ρ u n) + slgFlux ρ u n ^ 2|
        ≤ |ρ n * (u n * slgFlux ρ u n)| + slgFlux ρ u n ^ 2 := by
      calc |ρ n * (u n * slgFlux ρ u n) + slgFlux ρ u n ^ 2|
          ≤ |ρ n * (u n * slgFlux ρ u n)| + |slgFlux ρ u n ^ 2| := abs_add_le _ _
        _ = |ρ n * (u n * slgFlux ρ u n)| + slgFlux ρ u n ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg (slgFlux ρ u n))]
    have hb2 : |ρ n * (u n * slgFlux ρ u n)| ≤ ρ n * (2 * slgNormalizedEnergy ρ Q u n) := by
      rw [abs_mul, abs_of_pos hρ]
      exact mul_le_mul_of_nonneg_left hmix hρ.le
    have hb3 : slgFlux ρ u n ^ 2 ≤ ρ n * (2 * slgNormalizedEnergy ρ Q u n) := by
      have : slgEnergy ρ Q u n ≤ ρ n * slgNormalizedEnergy ρ Q u n := by
        rw [hEF]
        nlinarith [hF, hsw]
      linarith
    linarith
  have hfinal : ρ n * |slgPrimitive ρ u n| ≤ ρ n * (4 * slgNormalizedEnergy ρ Q u n) := by
    have hrw : ρ n * |slgPrimitive ρ u n| = |ρ n * slgPrimitive ρ u n| := by
      rw [abs_mul, abs_of_pos hρ]
    rw [hrw]
    exact habs
  exact le_of_mul_le_mul_left hfinal hρ

/-! ## The control coefficient and the bootstrap -/

/-- The drift against which the virial primitive is Abel-summed. -/
noncomputable def slgAbelDrift (ρ Q : ℕ → ℝ) (n : ℕ) : ℝ := slgDrift ρ Q n * ρ n

/-- The per-step control coefficient of the Liouville--Green bootstrap. -/
noncomputable def slgControl (ρ Q : ℕ → ℝ) (n : ℕ) : ℝ :=
  |slgDrift ρ Q n| * Q n
    + |slgDrift ρ Q n| * |slgRatioDefect ρ Q n| * Real.sqrt (slgWeight ρ Q n)
    + 4 * (|Q (n + 1)| * |ρ (n + 1) - ρ n|) / (ρ n * Real.sqrt (slgWeight ρ Q (n + 1)))

theorem slgControl_nonneg (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) : 0 ≤ slgControl ρ Q n := by
  unfold slgControl
  have h1 : (0:ℝ) ≤ |slgDrift ρ Q n| * Q n := mul_nonneg (abs_nonneg _) hQ
  have h2 : (0:ℝ)
      ≤ |slgDrift ρ Q n| * |slgRatioDefect ρ Q n| * Real.sqrt (slgWeight ρ Q n) := by positivity
  have h3 : (0:ℝ)
      ≤ 4 * (|Q (n + 1)| * |ρ (n + 1) - ρ n|) / (ρ n * Real.sqrt (slgWeight ρ Q (n + 1))) := by
    apply div_nonneg (by positivity)
    exact mul_nonneg hρ.le (Real.sqrt_nonneg _)
  linarith

/-- **Pointwise bound on the non-virial part of one normalized-energy increment.** -/
theorem slg_increment_tail_bound (h : IsSLGSolution ρ Q u) {n : ℕ}
    (hρ : 0 < ρ n) (hQ : 0 ≤ Q n) (hQρ : Q n ≤ ρ n)
    (hW : 0 < slgWeight ρ Q n) (hW' : 0 < slgWeight ρ Q (n + 1)) :
    |slgNormalizedEnergy ρ Q u (n + 1) - slgNormalizedEnergy ρ Q u n
        - slgDrift ρ Q n * (slgVirial ρ Q u n / 2)|
      ≤ slgControl ρ Q n * slgNormalizedEnergy ρ Q u n := by
  have hF := slgNormalizedEnergy_nonneg (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith)
  have hEF := slgEnergy_eq_normalized (ρ := ρ) (Q := Q) (u := u) (n := n) hW
  have hmix := abs_mul_slgFlux_le (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ (by linarith) hW
  have hP := abs_slgPrimitive_le (ρ := ρ) (Q := Q) (u := u) (n := n) hρ hQ hQρ hW
  have hsplit := slgNormalizedEnergy_succ_sub_split h hρ hW hW'
  have hs' : 0 < Real.sqrt (slgWeight ρ Q (n + 1)) := Real.sqrt_pos.mpr hW'
  have key : slgNormalizedEnergy ρ Q u (n + 1) - slgNormalizedEnergy ρ Q u n
      - slgDrift ρ Q n * (slgVirial ρ Q u n / 2)
      = -(slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2))
        + slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n
        + slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1)) := by
    rw [hsplit]; ring
  rw [key]
  have h1 : |(-(slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2)))|
      ≤ |slgDrift ρ Q n| * Q n * slgNormalizedEnergy ρ Q u n := by
    rw [abs_neg, abs_mul]
    have hhalf : |Q n * (u n * slgFlux ρ u n) / 2| ≤ Q n * slgNormalizedEnergy ρ Q u n := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul, abs_of_nonneg hQ]
      have := mul_le_mul_of_nonneg_left hmix hQ
      linarith
    calc |slgDrift ρ Q n| * |Q n * (u n * slgFlux ρ u n) / 2|
        ≤ |slgDrift ρ Q n| * (Q n * slgNormalizedEnergy ρ Q u n) :=
          mul_le_mul_of_nonneg_left hhalf (abs_nonneg _)
      _ = |slgDrift ρ Q n| * Q n * slgNormalizedEnergy ρ Q u n := by ring
  have h2 : |slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n|
      ≤ |slgDrift ρ Q n| * |slgRatioDefect ρ Q n| * Real.sqrt (slgWeight ρ Q n)
        * slgNormalizedEnergy ρ Q u n := by
    rw [abs_mul, abs_mul, hEF, abs_mul, abs_of_nonneg hF,
      abs_of_nonneg (Real.sqrt_nonneg (slgWeight ρ Q n))]
    apply le_of_eq
    ring
  have h3 : |slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1))|
      ≤ 4 * (|Q (n + 1)| * |ρ (n + 1) - ρ n|) / (ρ n * Real.sqrt (slgWeight ρ Q (n + 1)))
        * slgNormalizedEnergy ρ Q u n := by
    have hme := mul_slgExtra ρ Q u n
    have hEabs : ρ n * |slgExtra ρ Q u n|
        ≤ |Q (n + 1)| * |ρ (n + 1) - ρ n| * (4 * slgNormalizedEnergy ρ Q u n) := by
      have hrw : ρ n * |slgExtra ρ Q u n| = |ρ n * slgExtra ρ Q u n| := by
        rw [abs_mul, abs_of_pos hρ]
      rw [hrw, hme, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hP (by positivity)
    have hEle : |slgExtra ρ Q u n|
        ≤ |Q (n + 1)| * |ρ (n + 1) - ρ n| * (4 * slgNormalizedEnergy ρ Q u n) / ρ n := by
      rw [le_div_iff₀ hρ]
      linarith [hEabs]
    rw [abs_div, abs_of_pos hs']
    rw [div_le_iff₀ hs']
    have hrhs : 4 * (|Q (n + 1)| * |ρ (n + 1) - ρ n|)
          / (ρ n * Real.sqrt (slgWeight ρ Q (n + 1))) * slgNormalizedEnergy ρ Q u n
          * Real.sqrt (slgWeight ρ Q (n + 1))
        = |Q (n + 1)| * |ρ (n + 1) - ρ n| * (4 * slgNormalizedEnergy ρ Q u n) / ρ n := by
      field_simp
    rw [hrhs]
    exact hEle
  calc |(-(slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2)))
          + slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n
          + slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1))|
      ≤ |(-(slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2)))
            + slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n|
          + |slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1))| := abs_add_le _ _
    _ ≤ (|(-(slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2)))|
            + |slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n|)
          + |slgExtra ρ Q u n / Real.sqrt (slgWeight ρ Q (n + 1))| := by
        have := abs_add_le (-(slgDrift ρ Q n * (Q n * (u n * slgFlux ρ u n) / 2)))
          (slgDrift ρ Q n * slgRatioDefect ρ Q n * slgEnergy ρ Q u n)
        linarith
    _ ≤ slgControl ρ Q n * slgNormalizedEnergy ρ Q u n := by
        rw [slgControl]
        have : (|slgDrift ρ Q n| * Q n
              + |slgDrift ρ Q n| * |slgRatioDefect ρ Q n| * Real.sqrt (slgWeight ρ Q n)
              + 4 * (|Q (n + 1)| * |ρ (n + 1) - ρ n|)
                / (ρ n * Real.sqrt (slgWeight ρ Q (n + 1)))) * slgNormalizedEnergy ρ Q u n
            = |slgDrift ρ Q n| * Q n * slgNormalizedEnergy ρ Q u n
              + |slgDrift ρ Q n| * |slgRatioDefect ρ Q n| * Real.sqrt (slgWeight ρ Q n)
                * slgNormalizedEnergy ρ Q u n
              + 4 * (|Q (n + 1)| * |ρ (n + 1) - ρ n|)
                / (ρ n * Real.sqrt (slgWeight ρ Q (n + 1)))
                * slgNormalizedEnergy ρ Q u n := by ring
        rw [this]
        linarith

/-- **The discrete Sturm--Liouville Liouville--Green bootstrap.**  The Abel drift may be replaced
by any approximation `Dr` whose deviation `dev` is summable. -/
theorem slg_bootstrap (h : IsSLGSolution ρ Q u) {Dr dev : ℕ → ℝ} {N₀ : ℕ}
    (hρ : ∀ n, N₀ ≤ n → 0 < ρ n) (hQ : ∀ n, N₀ ≤ n → 0 < Q n)
    (hQρ : ∀ n, N₀ ≤ n → Q n ≤ ρ n)
    (hdev : ∀ n, N₀ ≤ n → |slgAbelDrift ρ Q n - Dr n| ≤ dev n)
    (hdev0 : ∀ n, N₀ ≤ n → 0 ≤ dev n)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |Dr n| ≤ 1 / 8)
    (hsum : ∀ K, ∑ k ∈ Finset.Ico N₀ K,
        (2 * |Dr (k + 1) - Dr k| + 2 * (slgControl ρ Q (k + 1) + 2 * dev (k + 1))) ≤ 1 / 8)
    {m : ℕ} (hm : N₀ ≤ m) :
    slgNormalizedEnergy ρ Q u m
      ≤ 2 * max (slgNormalizedEnergy ρ Q u N₀) (slgNormalizedEnergy ρ Q u (N₀ + 1)) := by
  have hWpos : ∀ n, N₀ ≤ n → 0 < slgWeight ρ Q n := fun n hn => mul_pos (hρ n hn) (hQ n hn)
  have hF0 : ∀ n, N₀ ≤ n → 0 ≤ slgNormalizedEnergy ρ Q u n := fun n hn =>
    slgNormalizedEnergy_nonneg (hρ n hn) (hQ n hn).le (by linarith [hQρ n hn, hρ n hn])
  have hPF : ∀ n, N₀ ≤ n → |slgPrimitive ρ u n| ≤ 4 * slgNormalizedEnergy ρ Q u n := fun n hn =>
    abs_slgPrimitive_le (hρ n hn) (hQ n hn).le (hQρ n hn) (hWpos n hn)
  refine abstract_energy_bootstrap
    (F := slgNormalizedEnergy ρ Q u) (P := slgPrimitive ρ u) (Dr := Dr)
    (ctrl := fun k => slgControl ρ Q (k + 1) + 2 * dev (k + 1)) hF0 hPF (fun k hk => ?_)
    (fun k hk => by
      have := slgControl_nonneg (ρ := ρ) (Q := Q) (n := k + 1) (hρ _ (by omega))
        (hQ _ (by omega)).le
      have := hdev0 (k + 1) (by omega)
      linarith)
    hbdry hsum hm
  have hk1 : N₀ ≤ k + 1 := by omega
  have hk2 : N₀ ≤ k + 2 := by omega
  have htail := slg_increment_tail_bound h (n := k + 1) (hρ _ hk1) (hQ _ hk1).le (hQρ _ hk1)
    (hWpos _ hk1) (hWpos _ hk2)
  have hvir := slgVirial_succ h k
  have hrw : slgDrift ρ Q (k + 1) * (slgVirial ρ Q u (k + 1) / 2)
      = slgAbelDrift ρ Q (k + 1) * (slgPrimitive ρ u (k + 1) - slgPrimitive ρ u k) / 2 := by
    rw [hvir, slgAbelDrift]
    ring
  rw [hrw] at htail
  have hextra : |(slgAbelDrift ρ Q (k + 1) - Dr (k + 1))
        * (slgPrimitive ρ u (k + 1) - slgPrimitive ρ u k) / 2|
      ≤ 2 * dev (k + 1)
        * (slgNormalizedEnergy ρ Q u k + slgNormalizedEnergy ρ Q u (k + 1)) := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    have hp : |slgPrimitive ρ u (k + 1) - slgPrimitive ρ u k|
        ≤ 4 * slgNormalizedEnergy ρ Q u (k + 1) + 4 * slgNormalizedEnergy ρ Q u k := by
      refine le_trans (abs_sub _ _) ?_
      linarith [hPF (k + 1) hk1, hPF k hk]
    have hd := hdev (k + 1) hk1
    have hd0 := hdev0 (k + 1) hk1
    have := mul_le_mul hd hp (abs_nonneg _) hd0
    linarith
  have hdecomp : slgNormalizedEnergy ρ Q u (k + 2) - slgNormalizedEnergy ρ Q u (k + 1)
      - Dr (k + 1) * (slgPrimitive ρ u (k + 1) - slgPrimitive ρ u k) / 2
      = (slgNormalizedEnergy ρ Q u (k + 2) - slgNormalizedEnergy ρ Q u (k + 1)
          - slgAbelDrift ρ Q (k + 1)
            * (slgPrimitive ρ u (k + 1) - slgPrimitive ρ u k) / 2)
        + (slgAbelDrift ρ Q (k + 1) - Dr (k + 1))
          * (slgPrimitive ρ u (k + 1) - slgPrimitive ρ u k) / 2 := by ring
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  have hFk := hF0 k hk
  have hFk1 := hF0 (k + 1) hk1
  have hc0 := slgControl_nonneg (ρ := ρ) (Q := Q) (n := k + 1) (hρ _ hk1) (hQ _ hk1).le
  nlinarith [htail, hextra, hc0, hFk, hFk1]

/-- **The Liouville--Green amplitude bound**: `u_n² ≲ 1/√(ρ_n Q_n)`. -/
theorem sq_le_of_slgControl (h : IsSLGSolution ρ Q u) {Dr dev : ℕ → ℝ} {N₀ : ℕ}
    (hρ : ∀ n, N₀ ≤ n → 0 < ρ n) (hQ : ∀ n, N₀ ≤ n → 0 < Q n)
    (hQρ : ∀ n, N₀ ≤ n → Q n ≤ ρ n)
    (hdev : ∀ n, N₀ ≤ n → |slgAbelDrift ρ Q n - Dr n| ≤ dev n)
    (hdev0 : ∀ n, N₀ ≤ n → 0 ≤ dev n)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |Dr n| ≤ 1 / 8)
    (hsum : ∀ K, ∑ k ∈ Finset.Ico N₀ K,
        (2 * |Dr (k + 1) - Dr k| + 2 * (slgControl ρ Q (k + 1) + 2 * dev (k + 1))) ≤ 1 / 8)
    {m : ℕ} (hm : N₀ ≤ m) :
    u m ^ 2
      ≤ 4 * max (slgNormalizedEnergy ρ Q u N₀) (slgNormalizedEnergy ρ Q u (N₀ + 1))
          / Real.sqrt (slgWeight ρ Q m) := by
  have hρm := hρ m hm
  have hQm := hQ m hm
  have hW : 0 < slgWeight ρ Q m := mul_pos hρm hQm
  have hs : 0 < Real.sqrt (slgWeight ρ Q m) := Real.sqrt_pos.mpr hW
  have hs2 : Real.sqrt (slgWeight ρ Q m) ^ 2 = slgWeight ρ Q m := Real.sq_sqrt hW.le
  have hbound := slg_bootstrap h hρ hQ hQρ hdev hdev0 hbdry hsum hm
  have hEq := slgEnergy_eq_normalized (ρ := ρ) (Q := Q) (u := u) (n := m) hW
  have hsq := slgWeight_mul_sq_le (ρ := ρ) (Q := Q) (u := u) (n := m) hρm hQm.le
    (by linarith [hQρ m hm])
  set C : ℝ := max (slgNormalizedEnergy ρ Q u N₀) (slgNormalizedEnergy ρ Q u (N₀ + 1)) with hC
  have hE : slgEnergy ρ Q u m ≤ 2 * C * Real.sqrt (slgWeight ρ Q m) := by
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hbound hs.le
  have hkey : slgWeight ρ Q m * u m ^ 2 ≤ 4 * C * Real.sqrt (slgWeight ρ Q m) := by linarith
  rw [le_div_iff₀ hs]
  nlinarith [hkey, hs, hs2, sq_nonneg (u m)]

end GaloisForLFunctions.HTGeometry
