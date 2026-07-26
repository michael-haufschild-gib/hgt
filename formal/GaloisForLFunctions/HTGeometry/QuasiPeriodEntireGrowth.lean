import GaloisForLFunctions.HTGeometry.Hypertranscendence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Growth of a quasi-periodic entire function

A function reproduced by two `ℝ`-independent translations up to nonzero constant multipliers has
**exponential type**: the two steps form an `ℝ`-basis of `ℂ`, so every point differs from a point of
the compact fundamental parallelogram by an integer combination of the steps whose coefficients are
bounded by a multiple of the norm, and each step multiplies the value by a fixed constant.

* `quasiPeriodic_zsmul` — a constant-multiplier quasi-period iterates over `ℤ`;
* `quasiPeriodic_lattice` — and over the whole step lattice;
* `stepBasis` — the two steps as an `ℝ`-basis of `ℂ`, with bounded coordinate functionals;
* **`exists_exp_growth_bound_of_quasiperiods`** — `‖f z‖ ≤ K · exp (c ‖z‖)`.

This is the growth half of the statement that an entire function with constant multipliers over a
lattice cannot vanish: its zero set would be a full lattice coset, whose counting function grows
like `r²`, while Jensen's inequality bounds the zero count of a function of exponential type
linearly in `r`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Iterating the multiplier -/

/-- A constant-multiplier quasi-period iterates over the integers. -/
theorem quasiPeriodic_zsmul {f : ℂ → ℂ} {w c : ℂ} (hc : c ≠ 0)
    (h : ∀ z, f (z + w) = c * f z) (m : ℤ) (z : ℂ) :
    f (z + m • w) = c ^ m * f z := by
  have hback : ∀ u : ℂ, f (u + -w) = c⁻¹ * f u := by
    intro u
    have hz : u + -w + w = u := by ring
    have hu := h (u + -w)
    rw [hz] at hu
    rw [hu]
    field_simp
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hs : ((n : ℤ) + 1) • w = (n : ℤ) • w + w := by rw [add_smul, one_smul]
      rw [hs, ← add_assoc, h (z + (n : ℤ) • w), ih, zpow_add₀ hc]
      simp only [zpow_one]
      ac_rfl
  | pred n ih =>
      have hs : (-(n : ℤ) - 1) • w = (-(n : ℤ)) • w + -w := by rw [sub_smul, one_smul]; ring
      rw [hs, ← add_assoc, hback (z + (-(n : ℤ)) • w), ih, zpow_sub₀ hc]
      field_simp

/-- Both multipliers iterate over the whole step lattice. -/
theorem quasiPeriodic_lattice {f : ℂ → ℂ} {w₁ w₂ a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) (m n : ℤ) (z : ℂ) :
    f (z + m • w₁ + n • w₂) = a ^ m * b ^ n * f z := by
  rw [quasiPeriodic_zsmul hb h₂ n (z + m • w₁), quasiPeriodic_zsmul ha h₁ m z]
  ring

/-! ### The two steps as a real basis -/

/-- Two `ℝ`-independent complex numbers form an `ℝ`-basis of `ℂ`. -/
noncomputable def stepBasis {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) :
    Module.Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank hindep (by simp [Complex.finrank_real_complex])

theorem stepBasis_apply {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (i : Fin 2) :
    stepBasis hindep i = ![w₁, w₂] i := by
  rw [stepBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The coordinate functionals of a basis of `ℂ` over `ℝ` are bounded by the norm. -/
theorem exists_bound_stepBasis_repr {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂])
    (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |(stepBasis hindep).repr z i| ≤ C * ‖z‖ := by
  let L : ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun z => (stepBasis hindep).repr z i
      map_add' := by intro x y; simp
      map_smul' := by
        intro c x
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        rfl }
  let Lc : ℂ →L[ℝ] ℝ := ⟨L, LinearMap.continuous_of_finiteDimensional L⟩
  refine ⟨‖Lc‖, norm_nonneg _, fun z => ?_⟩
  have hle := Lc.le_opNorm z
  simpa [Lc, L, Real.norm_eq_abs] using hle

/-! ### Exponential type -/

/-- The absolute value of an integer power is bounded by the corresponding power of
`max ‖c‖ ‖c‖⁻¹`. -/
theorem norm_zpow_le_max_pow {c : ℂ} (m : ℤ) :
    ‖c ^ m‖ ≤ (max ‖c‖ ‖c‖⁻¹) ^ m.natAbs := by
  rcases m.natAbs_eq with hm | hm
  · rw [hm, zpow_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _
  · rw [hm, zpow_neg, zpow_natCast, norm_inv, norm_pow, ← inv_pow]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg c))
      (le_max_right ‖c‖ ‖c‖⁻¹) m.natAbs

/-- `1 ≤ max ‖c‖ ‖c‖⁻¹` for a nonzero `c`. -/
theorem one_le_max_norm_inv {c : ℂ} (hc : c ≠ 0) : 1 ≤ max ‖c‖ ‖c‖⁻¹ := by
  rcases le_total ‖c‖ 1 with hle | hle
  · exact le_max_of_le_right (one_le_inv_iff₀.mpr ⟨norm_pos_iff.mpr hc, hle⟩)
  · exact le_max_of_le_left hle

/-- **A quasi-periodic entire function has exponential type.** -/
theorem exists_exp_growth_bound_of_quasiperiods {f : ℂ → ℂ} (hcont : Continuous f)
    {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧ ∀ z, ‖f z‖ ≤ K * Real.exp (c * ‖z‖) := by
  classical
  -- the fundamental parallelogram, a compact set, and a bound for `f` on it
  have hPcompact : IsCompact ((fun p : ℝ × ℝ => p.1 • w₁ + p.2 • w₂) ''
      (Set.Icc 0 1 ×ˢ Set.Icc 0 1)) := by
    refine ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))).image ?_
    fun_prop
  obtain ⟨M, hM⟩ := hPcompact.exists_bound_of_continuousOn hcont.continuousOn
  have hzeroP : (0 : ℂ) ∈ (fun p : ℝ × ℝ => p.1 • w₁ + p.2 • w₂) ''
      (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := ⟨(0, 0), by constructor <;> simp, by simp⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ hzeroP)
  -- multiplier bounds
  have hA₁1 : 1 ≤ max ‖a‖ ‖a‖⁻¹ := one_le_max_norm_inv ha
  have hA₂1 : 1 ≤ max ‖b‖ ‖b‖⁻¹ := one_le_max_norm_inv hb
  have hlogA₁ : 0 ≤ Real.log (max ‖a‖ ‖a‖⁻¹) := Real.log_nonneg hA₁1
  have hlogA₂ : 0 ≤ Real.log (max ‖b‖ ‖b‖⁻¹) := Real.log_nonneg hA₂1
  -- coordinate bounds
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_stepBasis_repr hindep 0
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_stepBasis_repr hindep 1
  refine ⟨M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) + 1,
    C₁ * Real.log (max ‖a‖ ‖a‖⁻¹) + C₂ * Real.log (max ‖b‖ ‖b‖⁻¹), by positivity,
    by positivity, ?_⟩
  intro z
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (stepBasis hindep).repr z 0 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (stepBasis hindep).repr z 1 := ⟨_, rfl⟩
  have hzsum : z = s • w₁ + t • w₂ := by
    have hrep := (stepBasis hindep).sum_repr z
    rw [Fin.sum_univ_two, stepBasis_apply hindep 0, stepBasis_apply hindep 1] at hrep
    rw [hs, ht]
    simpa using hrep.symm
  -- the integer part of the coordinates
  have hu : z - ((⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂)
      = (s - (⌊s⌋ : ℝ)) • w₁ + (t - (⌊t⌋ : ℝ)) • w₂ := by
    rw [hzsum]
    simp only [sub_smul, zsmul_eq_mul, Complex.real_smul, Complex.ofReal_intCast]
    ring
  have humem : z - ((⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂) ∈
      (fun p : ℝ × ℝ => p.1 • w₁ + p.2 • w₂) '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
    refine ⟨(s - (⌊s⌋ : ℝ), t - (⌊t⌋ : ℝ)), ⟨⟨?_, ?_⟩, ?_, ?_⟩, hu.symm⟩
    · change 0 ≤ Int.fract s
      exact Int.fract_nonneg s
    · change Int.fract s ≤ 1
      exact (Int.fract_lt_one s).le
    · change 0 ≤ Int.fract t
      exact Int.fract_nonneg t
    · change Int.fract t ≤ 1
      exact (Int.fract_lt_one t).le
  have hval : f z = a ^ (⌊s⌋ : ℤ) * b ^ (⌊t⌋ : ℤ) *
      f (z - ((⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂)) := by
    have hlat := quasiPeriodic_lattice ha hb h₁ h₂ (⌊s⌋ : ℤ) (⌊t⌋ : ℤ)
      (z - ((⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂))
    rw [show z - ((⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂) + (⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂ = z by ring]
      at hlat
    exact hlat
  have hnorm : ‖f z‖ ≤ (max ‖a‖ ‖a‖⁻¹) ^ (⌊s⌋ : ℤ).natAbs *
      (max ‖b‖ ‖b‖⁻¹) ^ (⌊t⌋ : ℤ).natAbs * M := by
    rw [hval, norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul (norm_zpow_le_max_pow _) (norm_zpow_le_max_pow _)
        (norm_nonneg _) (by positivity))
      (hM _ humem) (norm_nonneg _) (by positivity)
  -- the integer coordinates are bounded by the norm
  have hcast : ∀ k : ℤ, ((k.natAbs : ℝ)) = |(k : ℝ)| := by
    intro k
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hfloor : ∀ (r : ℝ) (C : ℝ), |r| ≤ C * ‖z‖ → ((⌊r⌋ : ℤ).natAbs : ℝ) ≤ C * ‖z‖ + 1 := by
    intro r C hr
    rw [hcast]
    have h1 : ((⌊r⌋ : ℤ) : ℝ) ≤ r := Int.floor_le r
    have h2 : r - 1 < ((⌊r⌋ : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one r
      linarith
    have h3 : -|r| ≤ r := neg_abs_le r
    have h4 : r ≤ |r| := le_abs_self r
    rw [abs_le]
    constructor <;> linarith
  have hmz : (((⌊s⌋ : ℤ)).natAbs : ℝ) ≤ C₁ * ‖z‖ + 1 := by
    refine hfloor s C₁ ?_
    rw [hs]
    exact hC₁ z
  have hnz : (((⌊t⌋ : ℤ)).natAbs : ℝ) ≤ C₂ * ‖z‖ + 1 := by
    refine hfloor t C₂ ?_
    rw [ht]
    exact hC₂ z
  -- convert the integer powers into an exponential
  have hpow1 : (max ‖a‖ ‖a‖⁻¹) ^ ((⌊s⌋ : ℤ)).natAbs
      ≤ (max ‖a‖ ‖a‖⁻¹) ^ (C₁ * ‖z‖ + 1 : ℝ) := by
    rw [← Real.rpow_natCast (max ‖a‖ ‖a‖⁻¹) ((⌊s⌋ : ℤ)).natAbs]
    exact Real.rpow_le_rpow_of_exponent_le hA₁1 hmz
  have hpow2 : (max ‖b‖ ‖b‖⁻¹) ^ ((⌊t⌋ : ℤ)).natAbs
      ≤ (max ‖b‖ ‖b‖⁻¹) ^ (C₂ * ‖z‖ + 1 : ℝ) := by
    rw [← Real.rpow_natCast (max ‖b‖ ‖b‖⁻¹) ((⌊t⌋ : ℤ)).natAbs]
    exact Real.rpow_le_rpow_of_exponent_le hA₂1 hnz
  have hA₁pos : (0 : ℝ) < max ‖a‖ ‖a‖⁻¹ := lt_of_lt_of_le zero_lt_one hA₁1
  have hA₂pos : (0 : ℝ) < max ‖b‖ ‖b‖⁻¹ := lt_of_lt_of_le zero_lt_one hA₂1
  have hexp : (max ‖a‖ ‖a‖⁻¹) ^ (C₁ * ‖z‖ + 1 : ℝ) * (max ‖b‖ ‖b‖⁻¹) ^ (C₂ * ‖z‖ + 1 : ℝ) * M
      = M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) *
        Real.exp ((C₁ * Real.log (max ‖a‖ ‖a‖⁻¹) + C₂ * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) := by
    rw [Real.rpow_add hA₁pos, Real.rpow_add hA₂pos, Real.rpow_one, Real.rpow_one,
      Real.rpow_def_of_pos hA₁pos, Real.rpow_def_of_pos hA₂pos]
    have harg :
        (C₁ * Real.log (max ‖a‖ ‖a‖⁻¹) +
              C₂ * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖ =
          Real.log (max ‖a‖ ‖a‖⁻¹) * (C₁ * ‖z‖) +
            Real.log (max ‖b‖ ‖b‖⁻¹) * (C₂ * ‖z‖) := by
      ring
    rw [harg, Real.exp_add]
    ring
  calc ‖f z‖ ≤ (max ‖a‖ ‖a‖⁻¹) ^ ((⌊s⌋ : ℤ)).natAbs *
        (max ‖b‖ ‖b‖⁻¹) ^ ((⌊t⌋ : ℤ)).natAbs * M := hnorm
    _ ≤ (max ‖a‖ ‖a‖⁻¹) ^ (C₁ * ‖z‖ + 1 : ℝ) * (max ‖b‖ ‖b‖⁻¹) ^ (C₂ * ‖z‖ + 1 : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
    _ = M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) *
        Real.exp ((C₁ * Real.log (max ‖a‖ ‖a‖⁻¹) + C₂ * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) := hexp
    _ ≤ (M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) + 1) *
        Real.exp ((C₁ * Real.log (max ‖a‖ ‖a‖⁻¹) + C₂ * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) := by
        have hpos : (0 : ℝ) < Real.exp
          ((C₁ * Real.log (max ‖a‖ ‖a‖⁻¹) + C₂ * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) :=
          Real.exp_pos _
        nlinarith

end GaloisForLFunctions.HTGeometry
