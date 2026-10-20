import GaloisForLFunctions.BiScaleUncertainty.PowerNodeRemovalLaw

/-!
# The orbit law: blindness at the powers `q^j` with `d ∤ j`

Let `q ≥ 2`, `ℓ = log q`, `F(z) = γ(‖z‖/ℓ)` the folded symbol on `ℝ/2πℤ`, and for `d ≥ 1`
`F_d(z) = (1/d) Σ_{k<d} F(z + 2πk/d)` its average over the orbit of rotation by `2π/d`.

**Theorem** (`blindSymbolSlackOn_offMultiples_iff`). The exact blind symbol slack on
`{q^j : j ≥ 1, d ∤ j}` is `−min_z F_d(z)`; the same holds with zero pole mass.

* **Lower bound.** Blindness at every `q^j` with `d ∤ j` kills every Fourier coefficient of the
  phase measure off the multiples of `d`, so the phase measure is invariant under rotation by
  `2π/d` (Fourier uniqueness on the circle). The folded symbol therefore integrates to its orbit
  average, which is at least its minimum.
* **Attainment by an exact design.** Put spectral atoms at the folded radii of the orbit
  `θ* + 2πk/d` of a minimizer: the cosine mixture vanishes at every `jℓ` with `d ∤ j` exactly
  (`Σ_k cos(α + 2πjk/d) = 0`), for every envelope, so a wide envelope realizes `min F_d` with no
  discretization error.

Compared with the full power grid (exact slack `−m_q`, `m_q` the mean of `F`), the multiples of
`d`, i.e. the powers of `q^d`, are worth exactly `m_q − min F_d`.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Rotations of the circle -/

theorem fourier_add_apply (n : ℤ) (z a : AddCircle (2 * π)) :
    fourier n (z + a) = fourier n z * fourier n a := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    induction a using QuotientAddGroup.induction_on with
    | H y =>
      rw [← AddCircle.coe_add, fourier_coe_apply, fourier_coe_apply, fourier_coe_apply,
        ← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- The rotation by `2π/d`. -/
abbrev orbitStep (d : ℕ) : AddCircle (2 * π) := ((2 * π / d : ℝ) : AddCircle (2 * π))

theorem fourier_orbitStep_of_dvd {d : ℕ} (hd : 1 ≤ d) {n : ℤ} (hn : (d : ℤ) ∣ n) :
    fourier n (orbitStep d) = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [fourier_coe_apply]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have e : 2 * (π : ℂ) * I * (((d : ℤ) * m : ℤ) : ℂ) * ((2 * π / d : ℝ) : ℂ) / ((2 * π : ℝ) : ℂ) =
      (m : ℂ) * (2 * π * I) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    push_cast; field_simp
  rw [e, Complex.exp_int_mul_two_pi_mul_I]

/-- **Rotation invariance.** If the cosine moments of `G` vanish at every `nℓ` with `d ∤ n`, the
phase observables of `G` are invariant under rotation by `2π/d`. -/
theorem integral_mul_periodic_rotate_eq {G : ℝ → ℝ} (hGc : Continuous G) (hG0 : ∀ r, 0 ≤ G r)
    (hGi : Integrable G) {ℓ : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hcos : ∀ n : ℕ, 1 ≤ n → ¬ d ∣ n → ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = 0)
    {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) (heven : ∀ z, P (-z) = P z) :
    ∃ ν : Measure (AddCircle (2 * π)), IsFiniteMeasure ν ∧
      ∫ r, G r * P (phase ℓ r) = ∫ z, P z ∂ν ∧
      (∀ k : ℕ, ∫ z, P (z + k • orbitStep d) ∂ν = ∫ z, P z ∂ν) ∧
      ν Set.univ = ENNReal.ofReal (∫ r, G r) := by
  obtain ⟨ν, hνf, hνF, hνP⟩ := exists_phase_measure hGc hG0 hGi ℓ
  refine ⟨ν, hνf, hνP P hP heven, ?_, ?_⟩
  · have hrot : ν.map (fun z => z + orbitStep d) = ν := by
      haveI : IsFiniteMeasure (ν.map (fun z => z + orbitStep d)) := Measure.isFiniteMeasure_map _ _
      apply GaloisForLFunctions.HTGeometry.addCircle_measure_eq_of_fourier_integral_eq
      intro n
      rw [integral_map (measurable_add_const _).aemeasurable
        (map_continuous (fourier n)).aestronglyMeasurable]
      simp_rw [fourier_add_apply]
      rw [integral_mul_const]
      by_cases hdn : (d : ℤ) ∣ n
      · rw [fourier_orbitStep_of_dvd hd hdn, mul_one]
      · have h0 : ∫ z, fourier n z ∂ν = 0 := by
          rw [hνF]
          have e : ∀ r : ℝ, Real.cos (r * ((n : ℝ) * ℓ)) = Real.cos (r * ((n.natAbs : ℝ) * ℓ)) := by
            intro r
            rw [Nat.cast_natAbs, Int.cast_abs]
            rcases abs_choice (n : ℝ) with h | h <;> rw [h]
            rw [show r * (-(n : ℝ) * ℓ) = -(r * ((n : ℝ) * ℓ)) by ring, Real.cos_neg]
          simp_rw [e]
          have hn0 : n ≠ 0 := by rintro rfl; exact hdn (dvd_zero _)
          rw [hcos _ (by omega) (fun h => hdn (Int.natAbs_dvd_natAbs.mp (by simpa using h)))]
          simp
        rw [h0, zero_mul]
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : Continuous fun z => P (z + k • orbitStep d) := hP.comp (continuous_add_const _)
      rw [← ih, ← hrot, integral_map (measurable_add_const _).aemeasurable
        hc.aestronglyMeasurable]
      congr 1; ext z
      rw [succ_nsmul, add_assoc, add_comm (orbitStep d)]
  · have h1 := hνP (fun _ => 1) continuous_const (fun _ => rfl)
    simp only [mul_one, integral_const, smul_eq_mul] at h1
    rw [h1, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-! ### 2. The orbit average of the folded symbol -/

/-- The orbit average `F_d(z) = (1/d) Σ_{k<d} F(z + 2πk/d)` of the folded symbol. -/
def orbitAverage (q d : ℕ) (z : AddCircle (2 * π)) : ℝ :=
  (∑ k ∈ Finset.range d, foldedSymbol (Real.log q) (z + k • orbitStep d)) / d

theorem continuous_orbitAverage (q d : ℕ) : Continuous (orbitAverage q d) :=
  (continuous_finsetSum _ fun _ _ =>
    (continuous_foldedSymbol _).comp (continuous_add_const _)).div_const _

/-- The minimal orbit average. -/
def orbitMinimum (q d : ℕ) : ℝ := ⨅ z, orbitAverage q d z

theorem orbitMinimum_le (q d : ℕ) (z : AddCircle (2 * π)) : orbitMinimum q d ≤ orbitAverage q d z :=
  ciInf_le ((isCompact_univ.image (continuous_orbitAverage q d)).bddBelow.mono
    (by rintro _ ⟨w, rfl⟩; exact ⟨w, Set.mem_univ _, rfl⟩)) z

theorem exists_orbitAverage_eq_orbitMinimum (q d : ℕ) :
    ∃ z, orbitAverage q d z = orbitMinimum q d := by
  obtain ⟨z, -, hz⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (continuous_orbitAverage q d).continuousOn
  exact ⟨z, le_antisymm (le_ciInf fun w => hz (Set.mem_univ w)) (orbitMinimum_le q d z)⟩

/-! ### 3. The lower bound -/

/-- The powers `q^j` with `j ≥ 1` and `d ∤ j`. -/
abbrev offMultipleNodes (q d : ℕ) : Set ℕ := {n | ∃ j : ℕ, 1 ≤ j ∧ ¬ d ∣ j ∧ n = q ^ j}

theorem orbitMinimum_mul_massOf_le {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (hb : BlindOn (offMultipleNodes q d) c) :
    orbitMinimum q d * massOf c ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨G, hG⟩ : ∃ G, G = combinationSpectralDensity c := ⟨_, rfl⟩
  have hGc : Continuous G := hG ▸ continuous_combinationSpectralDensity c
  have hG0 : ∀ r, 0 ≤ G r := hG ▸ combinationSpectralDensity_nonneg hc
  have hGi : Integrable G := hG ▸ integrable_combinationSpectralDensity c
  have hcos : ∀ n : ℕ, 1 ≤ n → ¬ d ∣ n →
      ∫ r, G r * Real.cos (r * ((n : ℝ) * Real.log q)) = 0 := by
    intro n hn hdn
    rw [hG, integral_combinationSpectralDensity_mul_cos_pow c hq hn, hb _ ⟨n, hn, hdn, rfl⟩,
      mul_zero]
  obtain ⟨ν, hνf, hνP, hrot, hνuniv⟩ := integral_mul_periodic_rotate_eq hGc hG0 hGi hd hcos
    (continuous_foldedSymbol (Real.log q)) (foldedSymbol_neg (Real.log q))
  have hFi : ∀ k : ℕ, Integrable (fun z => foldedSymbol (Real.log q) (z + k • orbitStep d)) ν :=
    fun k => (BoundedContinuousFunction.mkOfCompact ⟨_,
      (continuous_foldedSymbol (Real.log q)).comp (continuous_add_const (k • orbitStep d))⟩).integrable ν
  have havg : ∫ z, foldedSymbol (Real.log q) z ∂ν = ∫ z, orbitAverage q d z ∂ν := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    rw [show (fun z => orbitAverage q d z) = fun z =>
      (∑ k ∈ Finset.range d, foldedSymbol (Real.log q) (z + k • orbitStep d)) / d from rfl,
      integral_div, integral_finsetSum _ fun k _ => hFi k]
    simp_rw [hrot]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hmin : orbitMinimum q d * (ν Set.univ).toReal ≤ ∫ z, orbitAverage q d z ∂ν := by
    have := integral_mono (integrable_const (orbitMinimum q d))
      ((BoundedContinuousFunction.mkOfCompact ⟨_, continuous_orbitAverage q d⟩).integrable ν)
      (fun z => orbitMinimum_le q d z)
    rwa [integral_const, smul_eq_mul, mul_comm, measureReal_def] at this
  rw [hνuniv, ENNReal.toReal_ofReal (integral_nonneg hG0)] at hmin
  have hGf : Integrable fun r => G r * foldedSymbol (Real.log q) (phase (Real.log q) r) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log q)).continuousOn
    exact integrable_mul_bounded hGi ((continuous_foldedSymbol _).comp (continuous_phase _))
      (C := C) fun r => by rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have iγ : Integrable fun r => G r * EF.gammaBracket r :=
    hG ▸ integrable_combinationSpectralDensity_mul_gammaBracket c
  have hmono := integral_mono hGf iγ fun r =>
    mul_le_mul_of_nonneg_left (foldedSymbol_phase_le hℓ r) (hG0 r)
  have hGm : ∫ r, G r = 2 * π * massOf c := hG ▸ integral_combinationSpectralDensity c
  have hGa : ∫ r, G r * EF.gammaBracket r = 2 * π * nodeArchOnly c :=
    hG ▸ integral_combinationSpectralDensity_mul_gammaBracket c
  rw [hνP, havg, hGa] at hmono
  rw [hGm] at hmin
  have hpi : 0 < 2 * π := by positivity
  nlinarith

/-! ### 4. Attainment by an exact design -/

/-- `Σ_{k<d} cos(α + 2πjk/d) = 0` when `d ∤ j`. -/
theorem sum_cos_orbit_eq_zero {d j : ℕ} (hd : 1 ≤ d) (hdj : ¬ d ∣ j) (α : ℝ) :
    ∑ k ∈ Finset.range d, Real.cos (α + 2 * π * j * k / d) = 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set β : ℝ := π * j / d with hβ
  have hsin : Real.sin β ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
    have hjm : (j : ℝ) = m * d := by
      rw [hβ] at hm; field_simp at hm; nlinarith [Real.pi_pos]
    have hm0 : 0 ≤ m := by
      by_contra hneg
      have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have : (j : ℝ) < 0 := by nlinarith
      linarith [Nat.cast_nonneg (α := ℝ) j]
    apply hdj
    refine ⟨m.toNat, ?_⟩
    have : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
    exact_mod_cast (show (j : ℝ) = d * m.toNat by rw [this, hjm]; ring)
  have htel : ∀ k : ℕ, 2 * Real.sin β * Real.cos (α + 2 * π * j * k / d) =
      Real.sin (α - β + 2 * β * ((k + 1 : ℕ) : ℝ)) - Real.sin (α - β + 2 * β * (k : ℝ)) := by
    intro k
    rw [Real.sin_sub_sin]
    have e1 : (α - β + 2 * β * ((k + 1 : ℕ) : ℝ) - (α - β + 2 * β * (k : ℝ))) / 2 = β := by
      push_cast; ring
    have e2 : (α - β + 2 * β * ((k + 1 : ℕ) : ℝ) + (α - β + 2 * β * (k : ℝ))) / 2 =
        α + 2 * π * j * k / d := by
      rw [hβ]; push_cast; field_simp; ring
    rw [e1, e2]
  have hsum : 2 * Real.sin β * ∑ k ∈ Finset.range d, Real.cos (α + 2 * π * j * k / d) = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => htel k,
      Finset.sum_range_sub (fun k : ℕ => Real.sin (α - β + 2 * β * (k : ℝ)))]
    have e : α - β + 2 * β * (d : ℝ) = (α - β) + (j : ℕ) * (2 * π) := by
      rw [hβ]; field_simp
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [e, Real.sin_add_nat_mul_two_pi, sub_self]
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero two_ne_zero hsin)

/-- **Attainment.** For every `ε > 0` there is a nonnegative combination blind at every `q^j`,
`d ∤ j`, whose archimedean part without the pole is at most `(min F_d + ε)` times its positive
mass. -/
theorem exists_blindOn_offMultiples_archOnly_le {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (offMultipleNodes q d) c ∧ 0 < massOf c ∧
      nodeArchOnly c ≤ (orbitMinimum q d + ε) * massOf c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨z₀, hz₀⟩ := exists_orbitAverage_eq_orbitMinimum q d
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective z₀
  obtain ⟨b, hb, hbc, hb0⟩ := exists_smooth_compact_source_positive_mass
  have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  obtain ⟨g, hg, hgc, hg0, hgE⟩ := exists_source_normalized_energy_lt (r := 2) le_rfl
    (hb.of_le hr) hbc hb0 hε
  set ω : ℕ → ℝ := fun k =>
    ‖((θ + 2 * π * k / d : ℝ) : AddCircle (2 * π))‖ / Real.log q with hω
  refine ⟨pairCombination hg hgc ω d, pairCombination_nonneg hg hgc ω d, ?_, ?_, ?_⟩
  · rintro ⟨n, hn2⟩ ⟨j, hj1, hdj, rfl⟩
    rw [nodeVector_pairCombination]
    have hlog : Real.log ((q ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log q := by
      rw [Nat.cast_pow, Real.log_pow]
    have e : ∀ k : ℕ, Real.cos (ω k * Real.log ((q ^ j : ℕ) : ℝ)) =
        Real.cos (θ * j + 2 * π * j * k / d) := by
      intro k
      rw [hlog, hω]
      have h1 : ‖((θ + 2 * π * k / d : ℝ) : AddCircle (2 * π))‖ / Real.log q *
          ((j : ℝ) * Real.log q) = (j : ℝ) * ‖((θ + 2 * π * k / d : ℝ) : AddCircle (2 * π))‖ := by
        field_simp
      rw [h1, ← circleCos_eq_cos_norm, circleCos_coe]
      congr 1; ring
    simp only [e]
    rw [sum_cos_orbit_eq_zero hd hdj, mul_zero]
  · rw [massOf_pairCombination]; positivity
  · have harch := nodeArchOnly_pairCombination_le hg hgc ω d
    rw [massOf_pairCombination]
    have hpt : ∀ k : ℕ, ((θ : AddCircle (2 * π)) + k • orbitStep d) =
        ((θ + 2 * π * k / d : ℝ) : AddCircle (2 * π)) := by
      intro k
      rw [orbitStep, ← AddCircle.coe_nsmul, ← AddCircle.coe_add, nsmul_eq_mul]
      congr 1; ring
    have e : ∀ k : ℕ, EF.gammaBracket (ω k) =
        foldedSymbol (Real.log q) ((θ : AddCircle (2 * π)) + k • orbitStep d) := by
      intro k
      rw [hpt]; rfl
    have hsum : ∑ k ∈ Finset.range d, EF.gammaBracket (ω k) = orbitMinimum q d * d := by
      simp only [e]
      have := hz₀
      unfold orbitAverage at this
      rwa [div_eq_iff hd0.ne'] at this
    rw [hsum] at harch
    have hJ : biScaleLevyEnergy g ≤ ε * autocorr g 0 := by
      have := hgE
      rw [normalizedArchEnergy, div_lt_iff₀ hg0] at this
      exact this.le
    have hJd := mul_le_mul_of_nonneg_left hJ hd0.le
    have e2 : (orbitMinimum q d + ε) * (d * autocorr g 0) =
        autocorr g 0 * (orbitMinimum q d * d) + d * (ε * autocorr g 0) := by ring
    rw [e2]
    linarith

/-! ### 5. The orbit law -/

theorem blindSymbolSlackOn_offMultiples {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    BlindSymbolSlackOn (offMultipleNodes q d) (-orbitMinimum q d) := fun c hc hb => by
  have := orbitMinimum_mul_massOf_le hq hd c hc hb
  linarith

/-- **The orbit law.** The exact blind symbol slack on `{q^j : d ∤ j}` is `−min F_d`. -/
theorem blindSymbolSlackOn_offMultiples_iff {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (M : ℝ) :
    BlindSymbolSlackOn (offMultipleNodes q d) M ↔ -orbitMinimum q d ≤ M := by
  refine ⟨fun h => ?_, fun h => (blindSymbolSlackOn_offMultiples hq hd).mono h⟩
  by_contra hlt
  rw [not_le] at hlt
  set g : ℝ := -orbitMinimum q d - M with hg
  have hgpos : 0 < g := by linarith
  obtain ⟨c, hc, hb, hm, ha⟩ := exists_blindOn_offMultiples_archOnly_le hq hd (half_pos hgpos)
  have h1 := h c hc hb
  have : (orbitMinimum q d + g / 2 + M) * massOf c < 0 := by
    have : orbitMinimum q d + g / 2 + M = -(g / 2) := by rw [hg]; ring
    rw [this]; nlinarith
  nlinarith

/-- The orbit law holds verbatim on zero-pole combinations. -/
theorem zeroPoleBlindSymbolSlackOn_offMultiples_iff {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (offMultipleNodes q d) M ↔ -orbitMinimum q d ≤ M := by
  have hsub : offMultipleNodes q d ⊆ powerNodes q := by
    rintro n ⟨j, hj, -, hn⟩
    exact ⟨j, hj, hn⟩
  rw [zeroPoleBlindSymbolSlackOn_iff_of_gapped ((gappedNodeSet_powers hq).mono hsub),
    blindSymbolSlackOn_offMultiples_iff hq hd]

/-- **The value of the multiples.** The powers of `q^d` are worth exactly `m_q − min F_d ≥ 0`. -/
theorem orbitMinimum_le_symbolPeriodMean {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    orbitMinimum q d ≤ symbolPeriodMean q := by
  have h1 : BlindSymbolSlackOn (powerNodes q) (-orbitMinimum q d) := fun c hc hb =>
    blindSymbolSlackOn_offMultiples hq hd c hc fun j hj => hb j (by
      obtain ⟨i, hi, -, hji⟩ := hj
      exact ⟨i, hi, hji⟩)
  have := (blindSymbolSlackOn_powers_iff hq _).mp h1
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
