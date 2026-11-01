import GaloisForLFunctions.CompletedArithmeticForms.ExceptionalConductorsVanishAbovePolylog
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap

/-!
# Polynomial-conductor complement coercivity and sharpened power-of-logarithm overlap positivity

This module proves four unconditional structural results on the complete Weil matrix
`completeWeilMatrix tiltedUnitSpline c N`:

1. **Polynomial-conductor orthogonal-complement coercivity and global negative-index ceiling.**
   For every polynomial conductor exponent `θ > 0` and every overlap exponent `0 < α < 1 / 16`,
   `completeWeilEnergy tiltedUnitSpline c N` satisfies the logarithmic coercivity bound
   `completeWeilEnergy tiltedUnitSpline c N z ≥ (c_orth * log N / c ^ 7) * ‖z‖ ^ 2` uniformly across
   `1 ≤ c ≤ (log N)^α` on the entire orthogonal complement `(conductorSubspace ⌊N^θ⌋₊ N)ᗮ`.
   Consequently, any subspace `U` of the full horizon space on which `completeWeilEnergy` is
   nonpositive on nonzero vectors has dimension `Module.finrank ℝ U ≤ ⌊N^θ⌋₊`.
2. **Summed-residual positivity criterion and sharp `O(m (1 + log m)^2)` complete-Weil residual.**
   Replacing the coarse `|c̃_m(j)| ≤ m` and `|J_m(j)| ≤ 2 m^2` envelopes across all eight blocks of
   `completeWeilMatrix_ramanujan_residual_eq_at_every_overlap` by `|c̃_m(j)| ≤ √φ(m) ≤ √m`,
   `|J_m(j)| ≤ 2 φ(m) (1 + log m)`, and collar-split Abel summation on `fullWeilCenterMatrix`
   lowers the single-mode residual norm square from `O(m^4)` to `O(m (1 + log m)^2)` for `m^2 ≤ N`.
   Together with `matrix_posDef_of_sum_conductor_residuals`, this lowers the low-band residual
   budget exponent from `5q + 19α` to `2q + 19α`.
3. **Defect-localized top-strip prime cross-pairing and `α < 2 / 71` all-vector positivity.**
   Splitting the `fullPrimeMatrix` off-diagonal action on `u ∈ conductorSubspace R' N` into its
   bounded bulk (`n ≤ N / R'^4` plus Mertens remainder) and its top strip `Ioc (N / R'^4) N`, and
   bounding the top-strip mass of `w ∈ (conductorSubspace R' N)ᗮ` by `poleDefect` via
   `log_mul_tail_mass_le_defect` while retaining full `c^9` tail coercivity, raises the
   unconditional all-vector positivity threshold from `1 / 59` to
   `sharpenedPowerLogExponent = 2 / 71` (`> 1 / 36`), together with its `c⁻⁷` spectral floor,
   literal `weilQuad` nonnegativity, and zero-mass-loss `poleDefect` reserve.
4. **Empty nonpositive conductor set across `1 ≤ m ≤ ⌊N^θ⌋₊`.**
   Combining `PosDef` below `⌈(log N)^9⌉₊` with `eventually_tiltedUnitSpline_exceptionalConductors_above_polylog_empty`
   eliminates every nonpositive Ramanujan conductor mode across `1 ≤ m ≤ ⌊N^θ⌋₊` for every
   `0 < θ < 1 / 2` and `0 < α < 2 / 71`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence SuccessorShellArithmetic

/-! ## Section 1: Polynomial-Conductor Orthogonal-Complement Coercivity -/

private theorem exists_matrix_polynomial_reserve_local :
    ∃ b B H : ℝ, 0 < b ∧ 0 < B ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          (b / c ^ 7) * poleDefect N (primeHorizonExtension x) - B * c ^ 9 * ‖x‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hr⟩ := exists_tiltedUnitSpline_complete_defect_reserve_polynomial
  refine ⟨b, B, H, hb, hB, hH, ?_⟩
  intro c hc N hN x
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := (mul_pos hH (pow_pos hc0 8)).trans_le hN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hN0)
  have hh := hr c hc N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at hh
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN1, integral_atomDilate_sq (div_pos hc0 hN0)]
  exact hh

private theorem starProjection_eq_zero_of_mem_orthogonal {N : ℕ}
    {K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N))}
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ Kᗮ) :
    K.starProjection z = 0 := by
  let p := K.starProjection z
  have hp_mem : p ∈ K := K.starProjection_apply_mem z
  have hi : ⟪p, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hp_mem hz
  have hi' : ⟪z, p⟫ = 0 := by simpa only [real_inner_comm] using hi
  have hj := K.starProjection_inner_eq_zero z p hp_mem
  rw [inner_sub_left] at hj
  change ⟪z, p⟫ - ⟪p, p⟫ = 0 at hj
  rw [hi', real_inner_self_eq_norm_sq] at hj
  apply norm_eq_zero.mp
  nlinarith only [hj, norm_nonneg p]

private theorem eventually_log_nat_le_rpow_36_local :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

/-- **Polynomial-conductor orthogonal-complement coercivity.**
For every `θ > 0` and `0 < α < 1 / 16`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
every vector `z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ` satisfies
`(c_orth * Real.log N / c ^ 7) * ‖z‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N z`. -/
theorem eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal
    {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hα_lt : α < 1 / 16) :
    ∃ c_orth : ℝ, 0 < c_orth ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ →
          (c_orth * Real.log (N : ℝ) / c ^ 7) * ‖z‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨b, B, H, hb, hB, hH, hres⟩ := exists_matrix_polynomial_reserve_local
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let c_orth := b * θ / (8 * D)
  have hc_orth : 0 < c_orth := by dsimp only [c_orth]; positivity
  refine ⟨c_orth, hc_orth, ?_⟩
  let μ := 1 - 16 * α
  have hμ : 0 < μ := by dsimp only [μ]; linarith only [hα_lt]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  let M_L := max 1 (max H (max (2 / θ) (4 * D / θ)))
  filter_upwards [hNθlim.eventually_ge_atTop 4,
    hLlim.eventually_ge_atTop M_L,
    ((tendsto_rpow_atTop hμ).comp hLlim).eventually_ge_atTop (B / c_orth + 1),
    eventually_log_nat_le_rpow_36_local,
    eventually_ge_atTop 2] with N hNθ4 hLM hLμ hLX hN2 c hc1 hcup z hz_orth
  dsimp only [Function.comp_def] at hNθ4 hLμ
  let L := Real.log (N : ℝ)
  let Q := ⌊(N : ℝ) ^ θ⌋₊
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLM
  have hHL : H ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLM
  have hL_2θ : 2 / θ ≤ L :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLM
  have hL_4Dθ : 4 * D / θ ≤ L :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLM
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcL : c ≤ L :=
    hcup.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα_lt] : α ≤ 1))
  have hHN : H * c ^ 8 ≤ (N : ℝ) := by
    let X := (N : ℝ) ^ (1 / 36 : ℝ)
    have hX1 : 1 ≤ X := hL1.trans hLX
    have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
      dsimp only [X]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have hHX : H ≤ X := hHL.trans hLX
    have hc8 : c ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hc0.le (hcL.trans hLX) 8
    calc
      H * c ^ 8 ≤ X * X ^ 8 := mul_le_mul hHX hc8 (by positivity) (by positivity)
      _ = X ^ 9 := by ring
      _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 9 ≤ 36)).trans_eq hX36
  by_cases hz0 : ‖z‖ = 0
  · have hz_eq : z = 0 := norm_eq_zero.mp hz0
    rw [hz_eq, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    unfold completeWeilEnergy
    rw [map_zero, inner_zero_left]
  · have hQ2 : 2 ≤ Q := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ (N : ℝ) ^ θ by linarith only [hNθ4]))
    have hQ_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ ≤ (Q : ℝ) := by
      have hgt : (N : ℝ) ^ θ - 1 < (Q : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
      linarith only [hNθ4, hgt]
    have hlogQ_lb : θ * L - 1 ≤ Real.log (Q : ℝ) := by
      have hlog2 : Real.log 2 ≤ 1 := by
        linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hpos : 0 < (N : ℝ) ^ θ := by linarith only [hNθ4]
      have h1 := Real.log_le_log (by positivity) hQ_half
      rw [Real.log_mul (by norm_num) hpos.ne', one_div, Real.log_inv, Real.log_rpow hN0] at h1
      linarith only [h1, hlog2]
    have hθL_ge2 : 2 ≤ θ * L := by
      have h := (div_le_iff₀ hθ).mp hL_2θ
      linarith only [h]
    have hθL_ge4D : 4 * D ≤ θ * L := by
      have h := (div_le_iff₀ hθ).mp hL_4Dθ
      linarith only [h]
    have hlogQ_half : (θ / 2) * L ≤ Real.log (Q : ℝ) := by
      linarith only [hlogQ_lb, hθL_ge2]
    have hgap_L : (θ / (4 * D)) * L ≤ Real.log (Q : ℝ) / D - 1 := by
      have hdiv := div_le_div_of_nonneg_right hlogQ_half hD.le
      have h1 : (θ / 2) * L / D = (θ / (2 * D)) * L := by ring
      have h2 : 1 ≤ (θ / (4 * D)) * L := by
        rw [div_mul_eq_mul_div, one_le_div (by positivity)]
        linarith only [hθL_ge4D]
      linarith only [hdiv, h1, h2]
    have hp0 : (conductorSubspace Q N).starProjection z = 0 :=
      starProjection_eq_zero_of_mem_orthogonal hz_orth
    have hdef : (Real.log (Q : ℝ) / D - 1) * ‖z‖ ^ 2 ≤ poleDefect N (primeHorizonExtension z) := by
      apply poleDefect_ge_explicit_of_norm_sub_starProjection_gt hQ2 hN2
      rw [hp0, sub_zero]
      have hp : 0 < ‖z‖ ^ 2 := sq_pos_of_ne_zero hz0
      linarith only [hp]
    have hdef_L : (2 * c_orth * L / c ^ 7) * ‖z‖ ^ 2 ≤
        (b / c ^ 7) * poleDefect N (primeHorizonExtension z) := by
      have h1 := mul_le_mul_of_nonneg_right hgap_L (sq_nonneg ‖z‖)
      have h2 := mul_le_mul_of_nonneg_left (h1.trans hdef) (div_nonneg hb.le (pow_pos hc0 7).le)
      have heq : (b / c ^ 7) * ((θ / (4 * D)) * L * ‖z‖ ^ 2) =
          (2 * c_orth * L / c ^ 7) * ‖z‖ ^ 2 := by
        dsimp only [c_orth]
        field_simp [hD.ne', hc0.ne']
        ring
      rwa [heq] at h2
    have hBc9_le : B * c ^ 9 ≤ c_orth * L / c ^ 7 := by
      rw [le_div_iff₀ (pow_pos hc0 7)]
      have hc16 : c ^ 16 ≤ L ^ (16 * α) := by
        have hp := pow_le_pow_left₀ hc0.le hcup 16
        have he : (L ^ α) ^ (16 : ℕ) = L ^ (16 * α) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
        exact hp.trans_eq he
      have hB_le : B ≤ c_orth * L ^ μ := by
        have h := (div_le_iff₀ hc_orth).mp (by linarith only [hLμ] : B / c_orth ≤ L ^ μ)
        linarith only [h]
      have hL_split : L ^ μ * L ^ (16 * α) = L := by
        rw [← Real.rpow_add hL0]
        have hexp : μ + 16 * α = 1 := by dsimp only [μ]; ring
        rw [hexp, Real.rpow_one]
      calc
        B * c ^ 9 * c ^ 7 = B * c ^ 16 := by ring
        _ ≤ (c_orth * L ^ μ) * L ^ (16 * α) :=
          mul_le_mul hB_le hc16 (by positivity) (by positivity)
        _ = c_orth * (L ^ μ * L ^ (16 * α)) := by ring
        _ = c_orth * L := by rw [hL_split]
    have hmass_le := mul_le_mul_of_nonneg_right hBc9_le (sq_nonneg ‖z‖)
    have hr := hres c hc1 N hHN z
    linarith only [hr, hdef_L, hmass_le]

/-- **Global polynomial-conductor ceiling on nonpositive subspaces.**
For every `θ > 0` and `0 < α < 1 / 16`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
every subspace `U` of `EuclideanSpace ℝ (PrimeHorizonIndex N)` on which `completeWeilEnergy` is
nonpositive on nonzero vectors satisfies `Module.finrank ℝ U ≤ ⌊(N : ℝ) ^ θ⌋₊`. -/
theorem eventually_completeWeil_global_negIndex_le_polynomialConductor
    {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hα_lt : α < 1 / 16) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ U : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)),
        (∀ z ∈ U, z ≠ 0 → completeWeilEnergy tiltedUnitSpline c N z ≤ 0) →
        Module.finrank ℝ U ≤ ⌊(N : ℝ) ^ θ⌋₊ := by
  let θ₀ := min θ (1 / 4)
  have hθ₀ : 0 < θ₀ := lt_min hθ (by norm_num)
  have hθ₀_le : θ₀ ≤ θ := min_le_left _ _
  have hθ₀_4 : θ₀ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨c_orth, hc_orth, horth⟩ :=
    eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal hθ₀ hα hα_lt
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₀) atTop atTop :=
    (tendsto_rpow_atTop hθ₀).comp tendsto_natCast_atTop_atTop
  filter_upwards [horth, hNθlim.eventually_ge_atTop 2, eventually_ge_atTop 3] with
    N horthN hNθ2 hN3 c hc1 hcup U hU
  dsimp only [Function.comp_def] at hNθ2
  have hN2 : 2 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let Q₀ := ⌊(N : ℝ) ^ θ₀⌋₊
  have hQ₀_mono : Q₀ ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1R hθ₀_le)
  have hQ₀_pos : 0 < Q₀ := Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ (N : ℝ) ^ θ₀ by linarith only [hNθ2]))
  have hQ₀_le : (Q₀ : ℝ) ≤ (N : ℝ) ^ θ₀ := Nat.floor_le (by positivity)
  have h2log : 2 * Real.log (Q₀ : ℝ) < Real.log (N : ℝ) := by
    have hlog_le : Real.log (Q₀ : ℝ) ≤ θ₀ * Real.log (N : ℝ) :=
      (Real.log_le_log (by exact_mod_cast hQ₀_pos) hQ₀_le).trans_eq (Real.log_rpow hN0 θ₀)
    have hhalf : 2 * (θ₀ * Real.log (N : ℝ)) ≤ (1 / 2) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hθ₀_4]) hL0.le |> fun h => by linarith only [h]
    linarith only [hlog_le, hhalf, hL0]
  have hinf_bot : U ⊓ (conductorSubspace Q₀ N)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hzne
    have hz_le := hU z hz.1 hzne
    have hz_ge := horthN c hc1 hcup hz.2
    have hpos : 0 < (c_orth * Real.log (N : ℝ) / c ^ 7) * ‖z‖ ^ 2 :=
      mul_pos (div_pos (mul_pos hc_orth hL0) (pow_pos hc0 7)) (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    linarith only [hz_le, hz_ge, hpos]
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq U ((conductorSubspace Q₀ N)ᗮ)
  rw [hinf_bot, Submodule.finrank_bot, add_zero] at hgrass
  have hsup_le : Module.finrank ℝ ↥(U ⊔ (conductorSubspace Q₀ N)ᗮ) ≤
      Module.finrank ℝ (conductorSubspace Q₀ N) +
        Module.finrank ℝ ↥((conductorSubspace Q₀ N)ᗮ) := by
    calc
      Module.finrank ℝ ↥(U ⊔ (conductorSubspace Q₀ N)ᗮ) ≤
          Module.finrank ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
        Submodule.finrank_le _
      _ = Module.finrank ℝ (conductorSubspace Q₀ N) +
            Module.finrank ℝ ↥((conductorSubspace Q₀ N)ᗮ) :=
        (Submodule.finrank_add_finrank_orthogonal (conductorSubspace Q₀ N)).symm
  have hfin_eq := finrank_conductorSubspace_eq hN2 h2log
  omega

/-! ## Section 2: Summed-Residual Positivity Criterion and Sharp `O(m (1 + log m)^2)` Residual -/

/-- A Hermitian matrix is positive definite whenever every normalized nonpositive eigenvector is
approximated within `1 / 4` squared `ℓ²` mass by conductors `1 ≤ m ≤ R ≤ Q` and the **summed**
conductor residual budget over `Icc 1 Q` is at most `e ^ 2 / 36`. -/
theorem matrix_posDef_of_sum_conductor_residuals {N R Q : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) {e : ℝ} (he : 0 < e)
    (hRQ : R ≤ Q) (hQ : 2 ≤ Q) (hQN : Q ^ 4 ≤ N)
    (hfloor : ∀ m ∈ Icc 1 Q, e ≤ E m)
    (happrox : ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ‖x‖ = 1 →
      ⟪Matrix.toEuclideanLin A x, x⟫ ≤ 0 →
      ∃ a : ℕ → ℝ, (∑ n ∈ Icc 1 N,
        (primeHorizonExtension x n -
          ∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4)
    (hbudget : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2) / e ^ 2 ≤ 1 / 36) :
    A.PosDef := by
  classical
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  by_contra hi
  have hi0 : hA.eigenvalues i ≤ 0 := le_of_not_gt hi
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have hh : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh, norm_nonneg x]
  have henergy : ⟪Matrix.toEuclideanLin A x, x⟫ ≤ 0 := by
    have hAx : Matrix.toEuclideanLin A x = hA.eigenvalues i • x := by
      ext j
      exact congrFun (hA.mulVec_eigenvectorBasis i) j
    rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
    exact hi0
  obtain ⟨a, ha⟩ := happrox x hx henergy
  have hmass := normalizedRamanujan_coordinate_mass_ge_of_raw_approximation
    hRQ hQ hQN x hx a ha
  have hterm : ∀ m ∈ Icc 1 Q,
      ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / e ^ 2 :=
    fun m hm => nonpositive_eigenvector_coordinate_sq_le_uniform_residual hA i hi0 he
      (hfloor m hm) (normalizedRamanujanHorizonVector m N)
  have hsum := sum_le_sum hterm
  rw [← sum_div] at hsum
  linarith only [hmass, hsum.trans hbudget]

private theorem abs_mode_le_sqrt_conductor {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt (m : ℝ) :=
  (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm n).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m))

private theorem normalized_action_sq_local (N m : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N)‖ ^ 2 / Real.log N := by
  rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

private theorem normalized_residual_sq_local (N m : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) (e : ℝ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
      e • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N) -
        e • ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
  simp only [normalizedRamanujanHorizonVector, map_smul]
  rw [smul_comm e (Real.sqrt (Real.log N))⁻¹, ← smul_sub,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

private theorem normalized_mode_norm_sq_le_linear {m N : ℕ}
    (hm : 0 < m) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 2 * (m : ℝ) := by
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hraw : ‖ramanujanHorizonVector m N‖ ^ 2 ≤ (m : ℝ) * (1 + Real.log N) := by
    rw [ramanujanHorizonVector_norm_sq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (m : ℝ) * (1 / (n : ℝ)) := by
        refine sum_le_sum fun n _ => ?_
        rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have hs := mul_self_le_mul_self (abs_nonneg (normalizedRamanujanMode m n))
          (abs_mode_le_sqrt_conductor hm n)
        rw [← sq, sq_abs, ← sq, Real.sq_sqrt (Nat.cast_nonneg m)] at hs
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      _ = (m : ℝ) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) (Nat.cast_nonneg m)
  calc
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 =
        ‖ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
      rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, inv_pow, Real.sq_sqrt hL.le]
      ring
    _ ≤ (m : ℝ) * (1 + Real.log N) / Real.log N := div_le_div_of_nonneg_right hraw hL.le
    _ ≤ 2 * (m : ℝ) := by
      rw [div_le_iff₀ hL]
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hlog)]

/-- Sharp `O(m * (1 + log m)^2 / log N)` bound on the prime-matrix residual of mode `m`. -/
private theorem exists_primeResidual_linear_conductor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
  obtain ⟨B, hB, hbound⟩ := SignedArithmeticHodgeTheory.exists_uniform_ramanujanPrimeResidual_family_bound
  refine ⟨16 * B, by positivity, fun m hm N => ?_⟩
  let mpos : ℕ+ := ⟨m, hm⟩
  have hraw := hbound {mpos} (fun _ => 1) N
  simp only [sum_singleton, one_mul, one_pow, mul_one] at hraw
  have hraw' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 ≤
      B * SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2 := by
    rw [ramanujanHorizonVector_residual_norm_sq]
    exact hraw
  have hlog0 := Real.log_natCast_nonneg m
  have hfac : (1 + 4 * Real.log (m : ℝ)) ^ 2 ≤ 16 * (1 + Real.log (m : ℝ)) ^ 2 := by
    have h1 : 1 + 4 * Real.log (m : ℝ) ≤ 4 * (1 + Real.log (m : ℝ)) := by linarith only [hlog0]
    exact (pow_le_pow_left₀ (by positivity) h1 2).trans_eq (by ring)
  have htot : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hcost : SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2 ≤
      16 * ((m : ℝ) * (1 + Real.log m) ^ 2) := by
    rw [SignedArithmeticHodgeTheory.ramanujanResidualConductorCost, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    exact (mul_le_mul htot hfac (sq_nonneg _) (Nat.cast_nonneg m)).trans_eq (by ring)
  rw [normalized_residual_sq_local]
  exact div_le_div_of_nonneg_right
    (hraw'.trans ((mul_le_mul_of_nonneg_left hcost hB.le).trans_eq (by ring)))
    (Real.log_natCast_nonneg N)

/-- Sharp `O(m * c^2 / N^2)` bound on the self-error replacement of mode `m`. -/
private theorem exists_selfError_linear_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      1 ≤ N → 1 ≤ Real.log N → ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) →
        ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 := by
  let B : ℝ := Real.exp (1 / 2) / 2
  refine ⟨2 * B ^ 2, by dsimp only [B]; positivity, fun m hm N hN hlog c hc hcN => ?_⟩
  have hv := normalized_mode_norm_sq_le_linear hm hlog
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc hN hcN
  have hsq := mul_self_le_mul_self (abs_nonneg _) hs
  rw [← sq, sq_abs, ← sq] at hsq
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul hsq hv (sq_nonneg _) (sq_nonneg _)).trans_eq (by dsimp only [B]; ring)

/-- Sharp `O(m * c^4 / log N)` bound on the polar moment error of mode `m`. -/
private theorem exists_poleError_linear_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 0 < c →
      ∀ N : ℕ, 1 ≤ N → c ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 4 / Real.log N := by
  refine ⟨4 * (atomPoleMomentErrorConstant φ) ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hcN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hraw : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤
      4 * (atomPoleMomentErrorConstant φ) ^ 2 * (m : ℝ) * c ^ 4 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc hN hcN
    have hs := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at hs
    calc
      _ = ∑ n ∈ Icc 1 N, (atomPoleErrorCoefficient φ c N * ∑ j ∈ Icc 1 N,
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
        refine sum_congr rfl fun n _ => ?_
        rw [mul_sum]; congr 1
        exact sum_congr rfl fun j _ => by simp only [ramanujanPoleProfile]; ring
      _ ≤ 4 * (atomPoleErrorCoefficient φ c N) ^ 2 * (Real.sqrt m) ^ 2 * (N : ℝ) ^ 4 :=
        sum_sq_twoPoleKernel_poleProfile_le (Real.sqrt_nonneg m) N
          (fun j _ => abs_mode_le_sqrt_conductor hm j) _
      _ ≤ 4 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) ^ 2 *
          (m : ℝ) * (N : ℝ) ^ 4 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg m)]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg m)
        exact mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by field_simp [hN0.ne']
  rw [normalized_action_sq_local]
  exact div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

/-- Sharp `O(m * c^4 / log N)` bound on the separated archimedean cross error of mode `m`. -/
private theorem exists_crossError_linear_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 0 < c →
      ∀ N : ℕ, 1 ≤ N →
        ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 4 / Real.log N := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨(36 * K₀) ^ 2, sq_nonneg _, ?_⟩
  intro m hm c hc N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hraw : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤ (36 * K₀) ^ 2 * (m : ℝ) * c ^ 4 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hentry := fun (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) =>
      abs_separatedCrossError_le hφ hsupp hM hc hN hn hj
    have hb := sum_sq_kernel_poleProfile_le
      (mul_nonneg hK₀0 (sq_nonneg (c / (N : ℝ)))) hentry (Real.sqrt_nonneg m)
      (fun j _ => abs_mode_le_sqrt_conductor hm j)
    rw [Real.sq_sqrt (Nat.cast_nonneg m)] at hb
    change (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N,
      (if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) *
          (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) ≤ _
    exact hb.trans_eq (by field_simp [hN0.ne'])
  rw [normalized_action_sq_local]
  exact div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

/-- Sharp `O(m * c^5 / log N)` bound on the near-center replacement of mode `m`. -/
private theorem exists_nearCenter_linear_conductor_bound (φ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 2 * c ≤ (N : ℝ) →
        ‖nearCenterVector φ c N m‖ ^ 2 ≤ C * (m : ℝ) * c ^ 5 / Real.log N := by
  let A := |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨4 * (2 * Real.exp 2) ^ 3 * A ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hcN, hc0])
  have hα : |completeWeilPoleShift φ c| = c * |completeWeilPoleShift φ 1| := by
    have h1 : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
      unfold completeWeilPoleShift; ring
    rw [h1, abs_mul, abs_of_pos hc0]
  have hentry (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ nearRowIndices c N n) :
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j| ≤ A * Real.sqrt m * c := by
    obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
    have hn1 := (mem_Icc.mp hn).1
    have hj1 := (mem_Icc.mp hjN).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    let y := |Real.log j - Real.log n|
    have hkernel : archimedeanCenterKernel n j = _root_.RHTower.archLevyDensity y := by
      unfold archimedeanCenterKernel
      rw [if_neg (by push Not; exact ⟨Ne.symm hjn, by omega, by omega⟩)]
    have hgap : 1 / (N : ℝ) ≤ y := by
      have h := gap_div_le_abs_log_div hj1 hn1 hjn
      rw [Real.log_div hj0.ne' hn0.ne'] at h
      have hd : (1 : ℝ) ≤ |(j : ℝ) - n| := by
        rcases lt_or_gt_of_ne hjn with h' | h'
        · have hR : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr h')
          rw [abs_of_neg (by linarith only [hR])]; linarith only [hR]
        · have hR : (n : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr h')
          rw [abs_of_pos (by linarith only [hR])]; linarith only [hR]
      have hmax0 : 0 < max (j : ℝ) n := hj0.trans_le (le_max_left _ _)
      have hmaxN : max (j : ℝ) n ≤ N :=
        max_le (by exact_mod_cast (mem_Icc.mp hjN).2) (by exact_mod_cast (mem_Icc.mp hn).2)
      calc
        1 / (N : ℝ) ≤ 1 / max (j : ℝ) n := one_div_le_one_div_of_le hmax0 hmaxN
        _ ≤ |(j : ℝ) - n| / max (j : ℝ) n := div_le_div_of_nonneg_right hd hmax0.le
        _ ≤ y := h
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hgap
    have hy1 : y ≤ 1 := hlog.trans ((div_le_one hN0).mpr hcN)
    have hD0 : 0 < _root_.RHTower.archLevyDensity y := _root_.RHTower.archLevyDensity_pos hy0
    have hD : _root_.RHTower.archLevyDensity y ≤ N / 2 + Real.exp (1 / 2) / 4 := by
      refine (archLevyDensity_le_inv_two_mul_add hy0 hy1).trans ?_
      have : 1 / (2 * y) ≤ N / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have := (div_le_iff₀ hN0).mp hgap
        linarith
      linarith
    have hcoef : |completeWeilPoleShift φ c| / N * _root_.RHTower.archLevyDensity y ≤ A * c := by
      rw [hα, div_mul_eq_mul_div, div_le_iff₀ hN0]
      dsimp only [A]
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have he0 := Real.exp_pos (1 / 2)
      nlinarith only [hD, hN1R, he0, mul_nonneg (abs_nonneg (completeWeilPoleShift φ 1)) hc0.le]
    rw [hkernel, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hD0]
    exact (mul_le_mul hcoef (abs_mode_le_sqrt_conductor hm j) (abs_nonneg _)
      (by positivity)).trans_eq (by ring)
  rw [nearCenterVector_norm_sq]
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
  have hb := sum_near_div_sqrt_sq_le_small_width hc0 hN hw
    (fun n j => completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
      normalizedRamanujanMode m j) hentry
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at hb
  exact hb.trans_eq (by unfold linearNearRowRadius; ring)

/-- Sharp `O(φ(m) (1 + log m))` envelope on `ramanujanLogDivisorJet m n`. -/
private theorem abs_divisorJet_le_totient_log {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |ramanujanLogDivisorJet m n| ≤ 2 * (m.totient : ℝ) * (1 + Real.log m) := by
  have hmangoldt : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  have htri := abs_add_le (ramanujanLogDivisorJet m n - ArithmeticFunction.vonMangoldt m)
    (ArithmeticFunction.vonMangoldt m)
  rw [sub_add_cancel, abs_of_nonneg hmangoldt] at htri
  have henvelope := abs_ramanujanLogDivisorJet_sub_mean_le hm n
  have htot1 : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hvm : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hdiff := mul_le_mul_of_nonneg_left (tameDifferent_le_log hm) (Nat.cast_nonneg m.totient)
  nlinarith only [htri, henvelope, htot1, hlog0, hvm, hdiff]

/-- Sharp `O(m * (1 + log m)^2 * c^5 / log N)` bound on the totient-normalized downward source. -/
private theorem exists_downward_linear_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
          C * ((m : ℝ) * (1 + Real.log m) ^ 2) * c ^ 5 / Real.log N := by
  obtain ⟨Cp, hCp, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let R₀ : ℝ := 2 * Real.exp 2
  let E : ℝ := Cp + R₀ + 3
  have hE0 : 0 ≤ E := by dsimp only [E, R₀]; positivity
  let A_near : ℝ := 4 * R₀ ^ 3 * E ^ 2
  let B_ext : ℝ := (Real.exp 1 + 2) * (2 * (Real.exp 1 + 1)) ^ 2
  have hB_ext : 0 ≤ B_ext := by dsimp only [B_ext]; positivity
  refine ⟨2 * (A_near + B_ext), by dsimp only [A_near]; positivity, ?_⟩
  intro m hm c hc1 N hN hw1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have hlogc : |Real.log c| ≤ c := by
    rw [abs_of_nonneg (Real.log_nonneg hc1)]
    exact (Real.log_le_sub_one_of_pos hc0).trans (by linarith only [hc0])
  have hentry : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |nearGammaDownwardCoefficient φ c N m n j| ≤
        E * ((m.totient : ℝ) * (1 + Real.log m)) * c := by
    intro n hn j hj
    have hjN := (mem_filter.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      have h := (mem_filter.mp hj).2.2
      change |Real.log j - Real.log n| ≤ 2 * c / N at h
      simpa only [mul_div_assoc] using h
    let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
    let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
    have hrem : |a - Real.log (1 / (c / N)) * q| ≤ Cp := by
      simpa only [a, q, mul_div_assoc] using hpair (c / N) (div_pos hc0 hN0) hw1 n j hs
    have hq : |q| ≤ 1 := by
      have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
        (|Real.log j - Real.log n| / (c / N))
      change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
      dsimp only [q]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact h
    have hcm : |ramanujanLagCoefficient m j| ≤ (m.totient : ℝ) :=
      BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
    have hjb : |ramanujanLogDivisorJet m j| ≤ 2 * (m.totient : ℝ) * (1 + Real.log m) :=
      abs_divisorJet_le_totient_log hm j
    have hquot : (N : ℝ) / j ≤ linearNearRowRadius c :=
      (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc0 hn hj hw).2.2
    have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
      (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
    have hloghigh : Real.log N - Real.log j ≤ linearNearRowRadius c := by
      have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
      rw [Real.log_div hN0.ne' hj0.ne'] at h
      linarith only [h, hquot]
    have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ linearNearRowRadius c + |Real.log c| := by
      have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [hlogeq, show Real.log N - Real.log c - Real.log j =
        (Real.log N - Real.log j) - Real.log c by ring]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh])
    have heq : nearGammaDownwardCoefficient φ c N m n j =
        (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
        (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
        q * ramanujanLogDivisorJet m j := by
      rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
        (mem_Icc.mp hjN).1]
      dsimp only [a, q]; ring
    rw [heq]
    have h1 := mul_le_mul hrem hcm (abs_nonneg _) hCp
    have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _)
      (add_nonneg (by unfold linearNearRowRadius; positivity) (abs_nonneg _)))
      hcm (abs_nonneg _) (Nat.cast_nonneg m.totient)
    have h3 := mul_le_mul hq hjb (abs_nonneg _) zero_le_one
    simp only [mul_one, one_mul] at h2 h3
    have htri : |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
        (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
        q * ramanujanLogDivisorJet m j| ≤
        Cp * (m.totient : ℝ) + (linearNearRowRadius c + |Real.log c|) * (m.totient : ℝ) +
          2 * (m.totient : ℝ) * (1 + Real.log m) := by
      refine (abs_add_three _ _ _).trans ?_
      simp only [abs_mul]
      linarith only [h1, h2, h3]
    have hR_eq : linearNearRowRadius c = R₀ * c := by unfold linearNearRowRadius; dsimp only [R₀]; ring
    rw [hR_eq] at htri
    dsimp only [E]
    nlinarith only [htri, hlogc, hc1, hCp, htot_pos, h1m,
      mul_nonneg hCp (mul_nonneg htot_pos.le (sub_nonneg.mpr hc1)),
      mul_nonneg (show 0 ≤ Cp + R₀ + 1 by positivity)
        (mul_nonneg (mul_nonneg htot_pos.le (sub_nonneg.mpr h1m)) hc0.le),
      mul_nonneg (mul_nonneg htot_pos.le h1m) (sub_nonneg.mpr hc1)]
  have hnear_sq : ‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 5 / Real.log N := by
    rw [normalizedNearGammaDownwardVector_norm_sq]
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    have hb := sum_near_div_sqrt_sq_le_small_width hc0 hN hw
      (nearGammaDownwardCoefficient φ c N m) hentry
    exact hb.trans_eq (by unfold linearNearRowRadius; dsimp only [A_near, R₀]; ring)
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hext_sq : ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 5 / Real.log N := by
    rw [normalizedExteriorDownwardVector_norm_sq]
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    have hc35 := pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)
    have h1m_sq : 1 ≤ (1 + Real.log (m : ℝ)) ^ 2 := one_le_pow₀ h1m
    calc
      _ ≤ ((Real.exp 1 + 2) * (2 * m.totient * (Real.exp 1 + 1)) ^ 2) * c ^ 3 :=
        sum_actualExteriorDownwardRow_sq_le_polynomial hg.continuous hc1 hN hgsupp hG hw m
      _ = B_ext * (m.totient : ℝ) ^ 2 * 1 * c ^ 3 := by dsimp only [B_ext]; ring
      _ ≤ B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 5 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1m_sq (by positivity)) hc35
          (by positivity) (by positivity)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt htot_pos.le,
    normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0]
  have htri := norm_sub_le (normalizedNearGammaDownwardVector φ c N m)
    (normalizedExteriorDownwardVector φ c N m)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h2sq : ‖normalizedNearGammaDownwardVector φ c N m -
      normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      2 * (‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 +
        ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2) := by
    nlinarith only [hsq, sq_nonneg (‖normalizedNearGammaDownwardVector φ c N m‖ -
      ‖normalizedExteriorDownwardVector φ c N m‖)]
  calc
    (m.totient : ℝ)⁻¹ * ‖normalizedNearGammaDownwardVector φ c N m -
        normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      (m.totient : ℝ)⁻¹ * (2 * (A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 5 / Real.log N +
        B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 5 / Real.log N)) :=
      mul_le_mul_of_nonneg_left (h2sq.trans (mul_le_mul_of_nonneg_left
        (add_le_add hnear_sq hext_sq) zero_le_two)) (inv_nonneg.mpr htot_pos.le)
    _ = 2 * (A_near + B_ext) * ((m.totient : ℝ) * (1 + Real.log m) ^ 2) * c ^ 5 / Real.log N := by
      field_simp [htot_pos.ne']
    _ ≤ 2 * (A_near + B_ext) * ((m : ℝ) * (1 + Real.log m) ^ 2) * c ^ 5 / Real.log N := by
      apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by dsimp only [A_near]; positivity)
      exact mul_le_mul_of_nonneg_right htot_le (sq_nonneg _)

/-- Reflected Abel summation starting at integer gap `d ≥ 1`:
`|∑_{j=1}^{n-d} a(j) / (n - j)| ≤ B / d`. -/
private theorem abs_sum_Icc_div_sub_gap_le_local {a : ℕ → ℝ} {B : ℝ} {n d : ℕ}
    (hd : 1 ≤ d) (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ Icc 1 (n - d), a j / ((n : ℝ) - j)| ≤ B / d := by
  by_cases hnd : n ≤ d
  · have hemp : Icc 1 (n - d) = ∅ := by
      rw [Nat.sub_eq_zero_of_le hnd]; exact Icc_eq_empty (by omega)
    have hB0 : 0 ≤ B := by simpa only [Ico_self, sum_empty, abs_zero] using hB 0 0 le_rfl
    rw [hemp, sum_empty, abs_zero]; positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpartial : ∀ k ≤ n - d, |∑ i ∈ range k, a (n - d - i)| ≤ B := by
    intro k hk
    rw [← Nat.Ico_zero_eq_range,
      sum_Ico_reflect a 0 (show k ≤ n - d + 1 by omega)]
    exact hB _ _ (Nat.sub_le _ _)
  have hab := abs_sum_mul_le_of_finite_partial
    (g := fun i => a (n - d - i)) (w := fun i => 1 / ((d : ℝ) + i))
    (n - d) hpartial (fun i => by positivity)
    (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
  have heq : (∑ i ∈ range (n - d), 1 / ((d : ℝ) + i) * a (n - d - i)) =
      ∑ j ∈ Icc 1 (n - d), a j / ((n : ℝ) - j) := by
    refine sum_bij (fun i _ => n - d - i) ?_ ?_ ?_ ?_
    · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i₁ h1 i₂ h2 h
      have := mem_range.mp h1; have := mem_range.mp h2
      change n - d - i₁ = n - d - i₂ at h; omega
    · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      exact ⟨n - d - j, mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have hi' := mem_range.mp hi
      have hsub : (n : ℝ) - (n - d - i : ℕ) = (d : ℝ) + i := by
        rw [Nat.cast_sub (show i ≤ n - d by omega), Nat.cast_sub (by omega : d ≤ n)]
        ring
      rw [hsub]; ring
  rw [heq] at hab
  exact hab.trans_eq (by push_cast; ring)

/-- Harmonic sum bound `|∑_{j=1}^N c̃_m(j) / j| ≤ 2 * √m * (1 + log m)` for `2 ≤ m ≤ N`. -/
private theorem abs_sum_Icc_normalizedRamanujanMode_div_le_sqrt_log {m N : ℕ}
    (hm : 2 ≤ m) (hmN : m ≤ N) :
    |∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)| ≤
      2 * Real.sqrt m * (1 + Real.log m) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have hsm1 : 1 ≤ Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm1)
  have hsplit : Icc 1 N = Icc 1 m ∪ Icc (m + 1) N := by
    ext j; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 m) (Icc (m + 1) N) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Icc] at h1 h2; omega
  have hhead : |∑ j ∈ Icc 1 m, normalizedRamanujanMode m j / (j : ℝ)| ≤
      Real.sqrt m * (1 + Real.log m) := by
    calc
      |∑ j ∈ Icc 1 m, normalizedRamanujanMode m j / (j : ℝ)| ≤
          ∑ j ∈ Icc 1 m, |normalizedRamanujanMode m j / (j : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 m, Real.sqrt m * (1 / (j : ℝ)) := by
        refine sum_le_sum fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [abs_div, abs_of_pos hj0, div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right (abs_mode_le_sqrt_conductor (by omega) j) (by positivity)
      _ = Real.sqrt m * ∑ j ∈ Icc 1 m, 1 / (j : ℝ) := (mul_sum _ _ _).symm
      _ ≤ Real.sqrt m * (1 + Real.log m) :=
        mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log m)
          (Real.sqrt_nonneg m)
  have htail : |∑ j ∈ Icc (m + 1) N, normalizedRamanujanMode m j / (j : ℝ)| ≤ 1 := by
    by_cases hmN_eq : N < m + 1
    · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]; norm_num
    · have hpartial : ∀ k ≤ N - m,
          |∑ i ∈ range k, normalizedRamanujanMode m (m + 1 + i)| ≤ (m : ℝ) := by
        intro k _
        have hbij : (∑ i ∈ range k, normalizedRamanujanMode m (m + 1 + i)) =
            ∑ j ∈ Ico (m + 1) (m + 1 + k), normalizedRamanujanMode m j := by
          refine sum_bij (fun i _ => m + 1 + i) ?_ ?_ ?_ ?_
          · intro i hi; exact mem_Ico.mpr ⟨by omega, by linarith [mem_range.mp hi]⟩
          · intro i₁ _ i₂ _ h; dsimp only at h; omega
          · intro j hj; obtain ⟨h1, h2⟩ := mem_Ico.mp hj
            exact ⟨j - (m + 1), mem_range.mpr (by omega), by omega⟩
          · intro _ _; rfl
        rw [hbij]
        exact CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm (by omega)
      have hab := abs_sum_mul_le_of_finite_partial
        (g := fun i => normalizedRamanujanMode m (m + 1 + i))
        (w := fun i => 1 / ((m : ℝ) + 1 + i)) (N - m) hpartial (fun i => by positivity)
        (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
      have heq : (∑ i ∈ range (N - m),
          1 / ((m : ℝ) + 1 + i) * normalizedRamanujanMode m (m + 1 + i)) =
          ∑ j ∈ Icc (m + 1) N, normalizedRamanujanMode m j / (j : ℝ) := by
        refine sum_bij (fun i _ => m + 1 + i) ?_ ?_ ?_ ?_
        · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i₁ _ i₂ _ h; dsimp only at h; omega
        · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
          exact ⟨j - (m + 1), mem_range.mpr (by omega), by omega⟩
        · intro i _; push_cast; ring
      rw [heq] at hab
      calc
        |∑ j ∈ Icc (m + 1) N, normalizedRamanujanMode m j / (j : ℝ)| ≤
            (m : ℝ) * (1 / ((m : ℝ) + 1 + (0 : ℕ))) := hab
        _ = (m : ℝ) / ((m : ℝ) + 1) := by simp only [Nat.cast_zero, add_zero, mul_one_div]
        _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only)
  rw [hsplit, sum_union hdisj]
  have h1_le : 1 ≤ Real.sqrt m * (1 + Real.log m) := by nlinarith only [hsm1, h1m]
  exact (abs_add_le _ _).trans (by linarith only [hhead, htail, h1_le])

/-- Sharp `O(α^2 * m * (1 + log m)^2 / log N)` norm-square bound on `fullWeilCenterMatrix α N`
across all `1 ≤ m` with `m * m ≤ N` and `1 ≤ log N`. -/
private theorem fullWeilCenter_residual_linear_conductor_bound (α : ℝ) {m N : ℕ}
    (hm : 1 ≤ m) (hmN : m * m ≤ N) (hlogN : 1 ≤ Real.log N) :
    ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      742 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
  by_cases hm1_eq : m = 1
  · subst hm1_eq
    have hb := fullWeilCenter_residual_uniform_conductor_bound zero_lt_one α N
    simp only [Nat.cast_one, one_pow, mul_one, Real.log_one, add_zero] at hb ⊢
    exact hb.trans (div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg α])
      (Real.log_natCast_nonneg N))
  have hm2 : 2 ≤ m := by omega
  rw [if_neg hm1_eq, zero_smul, sub_zero]
  have hN4 : 4 ≤ N := (Nat.mul_le_mul hm2 hm2).trans hmN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hm_le_N : m ≤ N := (Nat.le_mul_self m).trans hmN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  let a := normalizedRamanujanMode m
  have ha_abs : ∀ j, |a j| ≤ (m : ℝ) := fun j => by
    dsimp only [a]
    have h1 := CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 (Nat.le_succ j)
    rwa [Nat.Ico_succ_singleton, sum_singleton] at h1
  have hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ (m : ℝ) :=
    fun _ _ hlk => CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 hlk
  let v := primeHorizonExtension (normalizedRamanujanHorizonVector m N)
  have hv_eq : ∀ j ∈ Icc 1 N, v j = (Real.sqrt (Real.log N))⁻¹ * (a j / Real.sqrt j) :=
    fun j hj => primeHorizonExtension_coe _ ⟨j, hj⟩
  -- Express `‖fullWeilCenterMatrix α N v_m‖ ^ 2` via row sums `row_pole n - row_col n`.
  let row_pole : ℕ → ℝ := fun n => ∑ j ∈ Icc 1 N, ((α / N) * arithmeticPoleKernel n j) * v j
  let row_col : ℕ → ℝ := fun n => ∑ j ∈ Icc 1 N, ((α / N) * archimedeanCenterKernel n j) * v j
  have hnorm_eq :
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
        ∑ n ∈ Icc 1 N, (row_pole n - row_col n) ^ 2 := by
    rw [normalized_action_sq_local]
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j =>
        (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 / Real.log N = _
    rw [horizonKernelMatrix_profile_norm_sq, div_eq_inv_mul,
      ← Real.sq_sqrt hL0.le, ← inv_pow, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [← mul_pow]
    congr 1
    dsimp only [row_pole, row_col]
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [hv_eq j hj, ramanujanPoleProfile]
    ring
  -- Part A: `∑ n ∈ Icc 1 N, row_pole n ^ 2 ≤ 10 * α^2 * m * (1 + log m)^2 / log N`.
  have hpole_sq : (∑ n ∈ Icc 1 N, row_pole n ^ 2) ≤
      10 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
    let S_m := ∑ j ∈ Icc 1 N, a j / (j : ℝ)
    let T_m := ∑ j ∈ Icc 1 N, a j
    have hS_abs : |S_m| ≤ 2 * Real.sqrt m * (1 + Real.log m) :=
      abs_sum_Icc_normalizedRamanujanMode_div_le_sqrt_log hm2 hm_le_N
    have hS_sq : S_m ^ 2 ≤ 4 * (m : ℝ) * (1 + Real.log m) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg _) hS_abs
      rw [← sq, sq_abs, ← sq, mul_pow, mul_pow, Real.sq_sqrt hm0.le] at h
      linarith only [h]
    have hT_abs : |T_m| ≤ (m : ℝ) := by
      have hIcc_Ico : Icc 1 N = Ico 1 (N + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
      dsimp only [T_m]; rw [hIcc_Ico]; exact hB 1 (N + 1) (by omega)
    have hT_sq : T_m ^ 2 ≤ (N : ℝ) := by
      have h1 := mul_self_le_mul_self (abs_nonneg _) hT_abs
      rw [← sq, sq_abs, ← sq] at h1
      exact h1.trans (by simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hmN)
    have hrow_p : ∀ n ∈ Icc 1 N, row_pole n =
        (Real.sqrt (Real.log N))⁻¹ * (α / N) * (Real.sqrt n * S_m + (1 / Real.sqrt n) * T_m) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      dsimp only [row_pole, S_m, T_m]
      rw [mul_add, mul_sum, mul_sum, mul_add, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      rw [hv_eq j hj]
      unfold arithmeticPoleKernel
      have hsj : Real.sqrt j * Real.sqrt j = (j : ℝ) := Real.mul_self_sqrt hj0.le
      field_simp [(Real.sqrt_pos.mpr hn0).ne', (Real.sqrt_pos.mpr hj0).ne',
        (Real.sqrt_pos.mpr hL0).ne']
      rw [hsj]
      ring
    have hpt_p : ∀ n ∈ Icc 1 N, row_pole n ^ 2 ≤
        2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * ((n : ℝ) * S_m ^ 2) +
          2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * (T_m ^ 2) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
      rw [hrow_p n hn, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hL0.le]
      have h2sq : (Real.sqrt n * S_m + 1 / Real.sqrt n * T_m) ^ 2 ≤
          2 * ((n : ℝ) * S_m ^ 2) + 2 * ((1 / (n : ℝ)) * T_m ^ 2) := by
        have h1 : (Real.sqrt n * S_m) ^ 2 = (n : ℝ) * S_m ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hn0.le]
        have h2 : (1 / Real.sqrt n * T_m) ^ 2 = (1 / (n : ℝ)) * T_m ^ 2 := by
          rw [mul_pow, one_div_pow, Real.sq_sqrt hn0.le]
        nlinarith only [h1, h2, sq_nonneg (Real.sqrt n * S_m - 1 / Real.sqrt n * T_m)]
      have hinv1 : (1 / (n : ℝ)) * T_m ^ 2 ≤ T_m ^ 2 :=
        (mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le zero_lt_one hn1) (sq_nonneg _)).trans_eq
          (by simp)
      have hc0_p : 0 ≤ (Real.log N)⁻¹ * (α / N) ^ 2 := by positivity
      calc
        (Real.log N)⁻¹ * (α / N) ^ 2 * (Real.sqrt n * S_m + 1 / Real.sqrt n * T_m) ^ 2 ≤
            (Real.log N)⁻¹ * (α / N) ^ 2 * (2 * ((n : ℝ) * S_m ^ 2) + 2 * T_m ^ 2) :=
          mul_le_mul_of_nonneg_left (h2sq.trans (by linarith only [hinv1])) hc0_p
        _ = 2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * ((n : ℝ) * S_m ^ 2) +
              2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * T_m ^ 2 := by
          field_simp [hN0.ne', hL0.ne']; ring
    have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
      calc
        (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
          sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
        _ = (N : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
    have hsum1 : (∑ n ∈ Icc 1 N, 2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * ((n : ℝ) * S_m ^ 2)) ≤
        8 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
      rw [← mul_sum, ← sum_mul]
      calc
        2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * ((∑ n ∈ Icc 1 N, (n : ℝ)) * S_m ^ 2) ≤
            2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * ((N : ℝ) ^ 2 *
              (4 * (m : ℝ) * (1 + Real.log m) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsum_n hS_sq (sq_nonneg _) (sq_nonneg _))
            (by positivity)
        _ = 8 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
          field_simp [hN0.ne', hL0.ne']; ring
    have hsum2 : (∑ n ∈ Icc 1 N, 2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * T_m ^ 2) ≤
        2 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      have hm1R : (1 : ℝ) ≤ (m : ℝ) * (1 + Real.log m) ^ 2 := by
        have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith only [hm_ge1, one_le_pow₀ h1m]
      calc
        (N : ℝ) * (2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * T_m ^ 2) ≤
            (N : ℝ) * (2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT_sq (by positivity)) hN0.le
        _ = 2 * α ^ 2 * 1 / Real.log N := by field_simp [hN0.ne', hL0.ne']; ring
        _ ≤ 2 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm1R (by positivity)) hL0.le
    calc
      (∑ n ∈ Icc 1 N, row_pole n ^ 2) ≤
          (∑ n ∈ Icc 1 N, 2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * ((n : ℝ) * S_m ^ 2)) +
            ∑ n ∈ Icc 1 N, 2 * (α ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) * T_m ^ 2 := by
        rw [← sum_add_distrib]; exact sum_le_sum hpt_p
      _ ≤ 8 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N +
            2 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N :=
        add_le_add hsum1 hsum2
      _ = 10 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by ring
  -- Part B: `∑ n ∈ Icc 1 N, row_col n ^ 2 ≤ 361 * α^2 * (1 + log m)^2 / log N`.
  let K_near : ℕ → ℕ → ℝ := fun n j =>
    if 2 * m < n ∧ j ≠ n ∧ (n < j + m ∧ j < n + m) then
      (α / N) * archimedeanCenterKernel n j else 0
  let row_near : ℕ → ℝ := fun n => ∑ j ∈ Icc 1 N, K_near n j * v j
  let row_far : ℕ → ℝ := fun n => row_col n - row_near n
  have hfar_sq : (∑ n ∈ Icc 1 N, row_far n ^ 2) ≤ 40 * α ^ 2 / Real.log N := by
    have hpt_far : ∀ n ∈ Icc 1 N,
        row_far n ^ 2 ≤
          if n ≤ 2 * m then 9 * α ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N)
          else 4 * α ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      by_cases hn2m : n ≤ 2 * m
      · rw [if_pos hn2m]
        have hzero : row_near n = 0 := sum_eq_zero fun j _ => by
          dsimp only [K_near]; rw [if_neg (by omega), zero_mul]
        have hcol_eq : row_col n = (Real.sqrt (Real.log N))⁻¹ *
            ((α / N) * ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a j / Real.sqrt j)) := by
          dsimp only [row_col]; rw [mul_sum, mul_sum]
          exact sum_congr rfl fun j hj => by rw [hv_eq j hj]; ring
        have hb := abs_sum_archimedeanCenterKernel_poleProfile_le hn hm0.le (ha_abs n) hB
        have h3m : (2 * (m : ℝ) + m) * Real.sqrt n = 3 * m * Real.sqrt n := by ring
        rw [h3m] at hb
        have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
        rw [← sq, sq_abs, ← sq, mul_pow, mul_pow, Real.sq_sqrt hn0.le] at hbsq
        have hrf : row_far n = row_col n := by dsimp only [row_far]; rw [hzero, sub_zero]
        rw [hrf, hcol_eq, mul_pow, inv_pow, Real.sq_sqrt hL0.le, mul_pow]
        calc
          (Real.log N)⁻¹ * ((α / N) ^ 2 *
              (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a j / Real.sqrt j)) ^ 2) ≤
              (Real.log N)⁻¹ * ((α / N) ^ 2 * (3 ^ 2 * (m : ℝ) ^ 2 * n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbsq (sq_nonneg _))
              (inv_nonneg.mpr hL0.le)
          _ = 9 * α ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) := by
            field_simp [hN0.ne', hL0.ne']; ring
      · rw [if_neg hn2m]
        have hn_gt : 2 * m < n := by omega
        let F_far := (Icc 1 N).filter (fun j => ¬(j ≠ n ∧ (n < j + m ∧ j < n + m)))
        have hfar_eq : row_far n = (Real.sqrt (Real.log N))⁻¹ * (α / N) *
            ∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j) := by
          have h1 : row_far n = ∑ j ∈ F_far, ((α / N) * archimedeanCenterKernel n j) * v j := by
            dsimp only [row_far, row_col, row_near, K_near, F_far]
            rw [sum_filter, ← sum_sub_distrib]
            refine sum_congr rfl fun j _ => ?_
            by_cases hcond : j ≠ n ∧ (n < j + m ∧ j < n + m)
            · rw [if_pos ⟨hn_gt, hcond⟩, if_neg (not_not.mpr hcond)]; ring
            · rw [if_neg (fun h => hcond h.2), if_pos hcond]; ring
          have hn_F : n ∈ F_far := mem_filter.mpr ⟨hn, fun h => h.1 rfl⟩
          have h2 : (∑ j ∈ F_far, ((α / N) * archimedeanCenterKernel n j) * v j) =
              (Real.sqrt (Real.log N))⁻¹ * (α / N) *
                ∑ j ∈ F_far, archimedeanCenterKernel n j * (a j / Real.sqrt j) := by
            rw [mul_sum]
            exact sum_congr rfl fun j hj => by rw [hv_eq j (mem_filter.mp hj).1]; ring
          rw [h1, h2, ← sum_erase_add F_far
            (fun j => archimedeanCenterKernel n j * (a j / Real.sqrt j)) hn_F,
            archimedeanCenterKernel_self, zero_mul, add_zero]
        have hF_er : F_far.erase n = Icc 1 (n - m) ∪ Icc (n + m) N := by
          ext j; simp only [F_far, mem_erase, mem_filter, mem_Icc, mem_union]; omega
        have hdisj_lu : Disjoint (Icc 1 (n - m)) (Icc (n + m) N) := by
          rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Icc] at h1 h2; omega
        have hdecomp_far :
            (∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j)) =
              Real.sqrt n / 2 * ((∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) - j)) +
                (∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n)) +
                (∑ j ∈ F_far.erase n, a j / ((n : ℝ) + j))) := by
          have hkern : ∀ j ∈ F_far.erase n,
              archimedeanCenterKernel n j * (a j / Real.sqrt j) =
                Real.sqrt n / 2 * (a j / |(n : ℝ) - j| + a j / ((n : ℝ) + j)) := by
            intro j hj
            obtain ⟨hjn, hjF⟩ := mem_erase.mp hj
            have hjI := (mem_filter.mp hjF).1
            have hk := archimedeanCenterKernel_div_sqrt_mul hn1 (mem_Icc.mp hjI).1 (Ne.symm hjn)
            calc
              archimedeanCenterKernel n j * (a j / Real.sqrt j) =
                  (archimedeanCenterKernel n j / Real.sqrt j) * a j := by ring
              _ = (Real.sqrt n / 2 * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j))) * a j := by rw [hk]
              _ = Real.sqrt n / 2 * (a j / |(n : ℝ) - j| + a j / ((n : ℝ) + j)) := by ring
          rw [sum_congr rfl hkern, ← mul_sum, sum_add_distrib]
          congr 1; rw [← add_assoc]; congr 1
          rw [hF_er, sum_union hdisj_lu]
          congr 1
          · refine sum_congr rfl fun j hj => ?_
            have hlt : (j : ℝ) < n := by exact_mod_cast (show j < n by have := (mem_Icc.mp hj).2; omega)
            rw [abs_of_pos (sub_pos.mpr hlt)]
          · refine sum_congr rfl fun j hj => ?_
            have hlt : (n : ℝ) < j := by exact_mod_cast (show n < j by have := (mem_Icc.mp hj).1; omega)
            rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]
        have hs_low : |∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) - j)| ≤ 1 :=
          (abs_sum_Icc_div_sub_gap_le_local (by omega : 1 ≤ m) hB).trans_eq (div_self hm0.ne')
        have hs_up : |∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n)| ≤ 1 := by
          by_cases hnmN : N < n + m
          · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]; norm_num
          · have hp : ∀ k ≤ N - (n + m) + 1, |∑ i ∈ range k, a (n + m + i)| ≤ (m : ℝ) := by
              intro k _
              have hb' : (∑ i ∈ range k, a (n + m + i)) = ∑ j ∈ Ico (n + m) (n + m + k), a j := by
                refine sum_bij (fun i _ => n + m + i) ?_ ?_ ?_ ?_
                · intro i hi; exact mem_Ico.mpr ⟨by omega, by linarith [mem_range.mp hi]⟩
                · intro i₁ _ i₂ _ h; dsimp only at h; omega
                · intro j hj; obtain ⟨h1, h2⟩ := mem_Ico.mp hj
                  exact ⟨j - (n + m), mem_range.mpr (by omega), by omega⟩
                · intro _ _; rfl
              rw [hb']; exact hB _ _ (by omega)
            have hab := abs_sum_mul_le_of_finite_partial
              (g := fun i => a (n + m + i)) (w := fun i => 1 / ((m : ℝ) + i))
              (N - (n + m) + 1) hp (fun i => by positivity)
              (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
            have heq : (∑ i ∈ range (N - (n + m) + 1), 1 / ((m : ℝ) + i) * a (n + m + i)) =
                ∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n) := by
              refine sum_bij (fun i _ => n + m + i) ?_ ?_ ?_ ?_
              · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
              · intro i₁ _ i₂ _ h; dsimp only at h; omega
              · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
                exact ⟨j - (n + m), mem_range.mpr (by omega), by omega⟩
              · intro i _; push_cast; ring
            rw [heq, Nat.cast_zero, add_zero] at hab
            exact hab.trans_eq (by field_simp [hm0.ne'])
        have hs_plus : |∑ j ∈ F_far.erase n, a j / ((n : ℝ) + j)| ≤ 2 := by
          rw [hF_er, sum_union hdisj_lu]
          have h1 : |∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) + j)| ≤ 1 := by
            have hb := abs_sum_Icc_div_add_le hn0.le hm0.le hB (n - m)
            have hle : (m : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr
              (by have : (m : ℝ) < n := by exact_mod_cast (show m < n by omega); linarith only [this])
            exact hb.trans hle
          have h2 : |∑ j ∈ Icc (n + m) N, a j / ((n : ℝ) + j)| ≤ 1 := by
            by_cases hnmN : N < n + m
            · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]; norm_num
            · have hp : ∀ k ≤ N - (n + m) + 1, |∑ i ∈ range k, a (n + m + i)| ≤ (m : ℝ) := by
                intro k _
                have hb' : (∑ i ∈ range k, a (n + m + i)) = ∑ j ∈ Ico (n + m) (n + m + k), a j := by
                  refine sum_bij (fun i _ => n + m + i) ?_ ?_ ?_ ?_
                  · intro i hi; exact mem_Ico.mpr ⟨by omega, by linarith [mem_range.mp hi]⟩
                  · intro i₁ _ i₂ _ h; dsimp only at h; omega
                  · intro j hj; obtain ⟨h1, h2⟩ := mem_Ico.mp hj
                    exact ⟨j - (n + m), mem_range.mpr (by omega), by omega⟩
                  · intro _ _; rfl
                rw [hb']; exact hB _ _ (by omega)
              have hab := abs_sum_mul_le_of_finite_partial
                (g := fun i => a (n + m + i)) (w := fun i => 1 / (2 * (n : ℝ) + m + i))
                (N - (n + m) + 1) hp (fun i => by positivity)
                (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
              have heq : (∑ i ∈ range (N - (n + m) + 1), 1 / (2 * (n : ℝ) + m + i) * a (n + m + i)) =
                  ∑ j ∈ Icc (n + m) N, a j / ((n : ℝ) + j) := by
                refine sum_bij (fun i _ => n + m + i) ?_ ?_ ?_ ?_
                · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
                · intro i₁ _ i₂ _ h; dsimp only at h; omega
                · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
                  exact ⟨j - (n + m), mem_range.mpr (by omega), by omega⟩
                · intro i _; push_cast; ring
              rw [heq, Nat.cast_zero, add_zero] at hab
              exact hab.trans ((div_le_one (by positivity)).mpr (by linarith only [hn0]) |>
                fun h => by simpa only [mul_one_div] using hab.trans h)
          exact (abs_add_le _ _).trans (by linarith only [h1, h2])
        have htot_far : |∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j)| ≤
            2 * Real.sqrt n := by
          rw [hdecomp_far, abs_mul, abs_of_pos (div_pos (Real.sqrt_pos.mpr hn0) zero_lt_two)]
          have htri := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
          have h4 : |∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) - j)| +
              |∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n)| +
              |∑ j ∈ F_far.erase n, a j / ((n : ℝ) + j)| ≤ 4 := by
            linarith only [hs_low, hs_up, hs_plus]
          calc
            Real.sqrt n / 2 * |_ + _ + _| ≤ Real.sqrt n / 2 * 4 :=
              mul_le_mul_of_nonneg_left (htri.trans h4) (by positivity)
            _ = 2 * Real.sqrt n := by ring
        have hsq_far := mul_self_le_mul_self (abs_nonneg _) htot_far
        rw [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt hn0.le] at hsq_far
        rw [hfar_eq, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hL0.le]
        calc
          (Real.log N)⁻¹ * (α / N) ^ 2 *
              (∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j)) ^ 2 ≤
              (Real.log N)⁻¹ * (α / N) ^ 2 * (2 ^ 2 * n) :=
            mul_le_mul_of_nonneg_left hsq_far (by positivity)
          _ = 4 * α ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) := by
            field_simp [hN0.ne', hL0.ne']; ring
    by_cases h2mN : 2 * m ≤ N
    · have hpart : Icc 1 N = Icc 1 (2 * m) ∪ Icc (2 * m + 1) N := by
        ext n; simp only [mem_Icc, mem_union]; omega
      have hdisj : Disjoint (Icc 1 (2 * m)) (Icc (2 * m + 1) N) := by
        rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc] at h1 h2; omega
      have hs1 : (∑ n ∈ Icc 1 (2 * m), row_far n ^ 2) ≤ 36 * α ^ 2 / Real.log N := by
        have hpt1 : ∀ n ∈ Icc 1 (2 * m),
            row_far n ^ 2 ≤ 18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N) := by
          intro n hn
          have hn2m := (mem_Icc.mp hn).2
          have hnR : (n : ℝ) ≤ 2 * m := by exact_mod_cast hn2m
          have h := hpt_far n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hn2m.trans h2mN⟩)
          rw [if_pos hn2m] at h
          exact h.trans (div_le_div_of_nonneg_right
            (by nlinarith only [hnR, sq_nonneg α, sq_nonneg (m : ℝ)]) (by positivity))
        have hsum1 := sum_le_sum hpt1
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat] at hsum1
        have hm4_le_N2 : (m : ℝ) ^ 4 ≤ (N : ℝ) ^ 2 := by
          have hm2N' : (m : ℝ) ^ 2 ≤ N := by
            simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hmN
          exact (show (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 by ring).trans_le
            (pow_le_pow_left₀ (by positivity) hm2N' 2)
        calc
          (∑ n ∈ Icc 1 (2 * m), row_far n ^ 2) ≤
              2 * (m : ℝ) * (18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N)) := hsum1
          _ = 36 * α ^ 2 * ((m : ℝ) ^ 4 / (N : ℝ) ^ 2) / Real.log N := by ring
          _ ≤ 36 * α ^ 2 * 1 / Real.log N :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
              ((div_le_one (sq_pos_of_pos hN0)).mpr hm4_le_N2) (by positivity)) hL0.le
          _ = 36 * α ^ 2 / Real.log N := by ring
      have hs2 : (∑ n ∈ Icc (2 * m + 1) N, row_far n ^ 2) ≤ 4 * α ^ 2 / Real.log N := by
        have hpt2 : ∀ n ∈ Icc (2 * m + 1) N,
            row_far n ^ 2 ≤ 4 * α ^ 2 / ((N : ℝ) * Real.log N) := by
          intro n hn
          obtain ⟨hn_lo, hn_hi⟩ := mem_Icc.mp hn
          have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn_hi
          have h := hpt_far n (mem_Icc.mpr ⟨by omega, hn_hi⟩)
          rw [if_neg (by omega)] at h
          calc
            row_far n ^ 2 ≤ 4 * α ^ 2 * (N : ℝ) / ((N : ℝ) ^ 2 * Real.log N) :=
              h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnR (by positivity))
                (by positivity))
            _ = 4 * α ^ 2 / ((N : ℝ) * Real.log N) := by field_simp [hN0.ne', hL0.ne']; ring
        have hsum2 := sum_le_sum hpt2
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc] at hsum2
        have hcard : ((N + 1 - (2 * m + 1) : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N + 1 - (2 * m + 1) ≤ N by omega)
        calc
          (∑ n ∈ Icc (2 * m + 1) N, row_far n ^ 2) ≤
              (N : ℝ) * (4 * α ^ 2 / ((N : ℝ) * Real.log N)) :=
            hsum2.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
          _ = 4 * α ^ 2 / Real.log N := by field_simp [hN0.ne', hL0.ne']
      rw [hpart, sum_union hdisj]
      linarith only [hs1, hs2]
    · exact absurd ((Nat.mul_le_mul_right m hm2).trans hmN) h2mN
  -- Near collar `L²` square bound via symmetric Schur majorant and linear-moment `v_m` square sum.
  have hnear_sq : (∑ n ∈ Icc 1 N, row_near n ^ 2) ≤
      128 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N := by
    let w_v : ℕ → ℝ := fun j => ((j : ℝ) / N) * |v j|
    let W_ker : ℕ → ℕ → ℝ := fun n j =>
      if j ≠ n ∧ (n < j + m ∧ j < n + m) then 2 * |α| / |(n : ℝ) - j| else 0
    have hrow_near_le : ∀ n ∈ Icc 1 N,
        |row_near n| ≤ ∑ j ∈ Icc 1 N, W_ker n j * w_v j := by
      intro n hn
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul]
      dsimp only [K_near, W_ker, w_v]
      by_cases hcond : 2 * m < n ∧ j ≠ n ∧ (n < j + m ∧ j < n + m)
      · rw [if_pos hcond, if_pos hcond.2]
        obtain ⟨_, hjn, _, _⟩ := hcond
        have hn1 := (mem_Icc.mp hn).1
        have hj1 := (mem_Icc.mp hj).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hjn_pos : 0 < |(n : ℝ) - j| :=
          abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hjn.symm))
        have hn_le_2j : (n : ℝ) ≤ 2 * j := by exact_mod_cast (show n ≤ 2 * j by omega)
        have hkern_le : archimedeanCenterKernel n j ≤ 2 * (j : ℝ) / |(n : ℝ) - j| := by
          have hk := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 (Ne.symm hjn)
          have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
          have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
          have heq : archimedeanCenterKernel n j =
              Real.sqrt n * Real.sqrt j / 2 * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) := by
            have := (div_eq_iff (mul_pos hsn hsj).ne').mp hk
            linarith only [this]
          have hadd_le : 1 / ((n : ℝ) + j) ≤ 1 / |(n : ℝ) - j| := by
            refine one_div_le_one_div_of_le hjn_pos ?_
            rw [abs_le]
            exact ⟨by linarith only [hn0, hj0], by linarith only [hn0, hj0]⟩
          have hsqrt_prod : Real.sqrt n * Real.sqrt j ≤ 2 * j := by
            have hsq : (Real.sqrt n * Real.sqrt j) ^ 2 ≤ (2 * (j : ℝ)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le]
              nlinarith only [hn_le_2j, hj0]
            nlinarith only [hsq, mul_nonneg hsn.le hsj.le, hj0]
          have hnonneg_kern : 0 ≤ archimedeanCenterKernel n j := by rw [heq]; positivity
          rw [heq]
          calc
            Real.sqrt n * Real.sqrt j / 2 * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) ≤
                Real.sqrt n * Real.sqrt j / 2 * (2 / |(n : ℝ) - j|) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              linarith only [hadd_le,
                (by ring : 1 / |(n : ℝ) - j| + 1 / |(n : ℝ) - j| = 2 / |(n : ℝ) - j|)]
            _ = Real.sqrt n * Real.sqrt j / |(n : ℝ) - j| := by ring
            _ ≤ 2 * (j : ℝ) / |(n : ℝ) - j| :=
              div_le_div_of_nonneg_right hsqrt_prod (abs_nonneg _)
        have hkern_nonneg : 0 ≤ archimedeanCenterKernel n j := by
          have hk := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 (Ne.symm hjn)
          have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
          have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
          have heq := (div_eq_iff (mul_pos hsn hsj).ne').mp hk
          have : 0 ≤ Real.sqrt n * Real.sqrt j *
              ((1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) / 2) := by positivity
          linarith only [heq, this]
        rw [abs_mul, abs_div, abs_of_pos hN0, abs_of_nonneg hkern_nonneg]
        calc
          (|α| / N) * archimedeanCenterKernel n j * |v j| ≤
              (|α| / N) * (2 * (j : ℝ) / |(n : ℝ) - j|) * |v j| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkern_le (by positivity)) (abs_nonneg _)
          _ = 2 * |α| / |(n : ℝ) - j| * ((j : ℝ) / N * |v j|) := by ring
      · rw [if_neg hcond, abs_zero, zero_mul]
        split_ifs <;> positivity
    have hW_symm : ∀ n j, W_ker n j = W_ker j n := fun n j => by
      dsimp only [W_ker]
      by_cases h : j ≠ n ∧ (n < j + m ∧ j < n + m)
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.2, h.2.1⟩, abs_sub_comm]
      · have h' : ¬(n ≠ j ∧ (j < n + m ∧ n < j + m)) :=
          fun hc => h ⟨hc.1.symm, hc.2.2, hc.2.1⟩
        rw [if_neg h, if_neg h']
    have hhar_m : (∑ d ∈ Icc 1 m, (1 : ℝ) / d) ≤ 2 * (1 + Real.log m) :=
      (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log m).trans (by linarith only [h1m])
    have hW_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, W_ker n j) ≤ 8 * |α| * (1 + Real.log m) := by
      intro n _
      let S_lo := (Icc 1 N).filter (fun j => j < n ∧ n < j + m)
      let S_hi := (Icc 1 N).filter (fun j => n < j ∧ j < n + m)
      have hsplit_W : (∑ j ∈ Icc 1 N, W_ker n j) =
          2 * |α| * ((∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) + ∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) := by
        have hdisj : Disjoint S_lo S_hi := by
          rw [Finset.disjoint_left]; intro j h1 h2
          simp only [S_lo, S_hi, mem_filter] at h1 h2; omega
        have heq_f : (Icc 1 N).filter (fun j => j ≠ n ∧ (n < j + m ∧ j < n + m)) =
            S_lo ∪ S_hi := by
          ext j
          simp only [S_lo, S_hi, mem_filter, mem_union]
          constructor
          · rintro ⟨hjI, hne, h1, h2⟩
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact Or.inl ⟨hjI, hlt, h1⟩
            · exact Or.inr ⟨hjI, hgt, h2⟩
          · rintro (⟨hjI, hlt, h1⟩ | ⟨hjI, hgt, h2⟩)
            · exact ⟨hjI, hlt.ne, h1, by omega⟩
            · exact ⟨hjI, hgt.ne', by omega, h2⟩
        dsimp only [W_ker]
        simp_rw [show ∀ j, (if j ≠ n ∧ (n < j + m ∧ j < n + m) then 2 * |α| / |(n : ℝ) - j| else 0) =
          2 * |α| * (if j ≠ n ∧ (n < j + m ∧ j < n + m) then 1 / |(n : ℝ) - j| else 0) from
          fun j => by split_ifs <;> ring]
        rw [← mul_sum, ← sum_filter, heq_f, sum_union hdisj]
      have hlo_le : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) ≤ 2 * (1 + Real.log m) := by
        have hinj : ∀ j₁ ∈ S_lo, ∀ j₂ ∈ S_lo, n - j₁ = n - j₂ → j₁ = j₂ := by
          intro j₁ h1 j₂ h2 heq
          have := (mem_filter.mp h1).2.1; have := (mem_filter.mp h2).2.1; omega
        have himg_sub : S_lo.image (fun j => n - j) ⊆ Icc 1 m := by
          intro d hd
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
          have := (mem_filter.mp hj).2; exact mem_Icc.mpr ⟨by omega, by omega⟩
        have heq_img : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) =
            ∑ d ∈ S_lo.image (fun j => n - j), (1 : ℝ) / d := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2.1
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)), Nat.cast_sub hlt.le]
        rw [heq_img]
        exact (sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity).trans hhar_m
      have hhi_le : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) ≤ 2 * (1 + Real.log m) := by
        have hinj : ∀ j₁ ∈ S_hi, ∀ j₂ ∈ S_hi, j₁ - n = j₂ - n → j₁ = j₂ := by
          intro j₁ h1 j₂ h2 heq
          have := (mem_filter.mp h1).2.1; have := (mem_filter.mp h2).2.1; omega
        have himg_sub : S_hi.image (fun j => j - n) ⊆ Icc 1 m := by
          intro d hd
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
          have := (mem_filter.mp hj).2; exact mem_Icc.mpr ⟨by omega, by omega⟩
        have heq_img : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) =
            ∑ d ∈ S_hi.image (fun j => j - n), (1 : ℝ) / d := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2.1
          rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hlt.le)), neg_sub,
            Nat.cast_sub hlt.le]
        rw [heq_img]
        exact (sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity).trans hhar_m
      rw [hsplit_W]
      calc
        2 * |α| * ((∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) + ∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) ≤
            2 * |α| * (2 * (1 + Real.log m) + 2 * (1 + Real.log m)) :=
          mul_le_mul_of_nonneg_left (add_le_add hlo_le hhi_le) (by positivity)
        _ = 8 * |α| * (1 + Real.log m) := by ring
    let B_W := 8 * |α| * (1 + Real.log m)
    have hBW0 : 0 ≤ B_W := by dsimp only [B_W]; positivity
    have hschur := CompletedArithmeticForms.sum_sq_abs_majorized_kernel_le' (N := N) W_ker W_ker w_v
      (fun _ => 1) (fun _ => B_W) (fun _ => B_W ^ 2)
      (fun n _ j _ => by dsimp only [W_ker]; split_ifs <;> positivity)
      (fun n _ j _ => (abs_of_nonneg (by dsimp only [W_ker]; split_ifs <;> positivity)).le)
      (fun _ _ => zero_lt_one)
      (fun n hn => by simpa only [mul_one] using hW_row n hn)
      (fun j hj => by
        have h1 : (∑ n ∈ Icc 1 N, W_ker n j * (B_W / 1)) = B_W * ∑ n ∈ Icc 1 N, W_ker j n := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hW_symm n j]; ring
        rw [h1]
        exact (mul_le_mul_of_nonneg_left (hW_row j hj) hBW0).trans_eq (sq B_W).symm)
    have hw_sq : (∑ j ∈ Icc 1 N, w_v j ^ 2) ≤ 2 / Real.log N := by
      have hpt1 : ∀ j ∈ Icc 1 N, w_v j ^ 2 ≤ ((j : ℝ) / N) * v j ^ 2 := by
        intro j hj
        have hjN : (j : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hj).2)
        have hj0 : 0 ≤ (j : ℝ) / N := by positivity
        dsimp only [w_v]
        rw [mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_right (by nlinarith only [hjN, hj0]) (sq_nonneg _)
      have hpt2 : ∀ j ∈ Icc 1 N, ((j : ℝ) / N) * v j ^ 2 =
          (1 / ((N : ℝ) * Real.log N)) * normalizedRamanujanMode m j ^ 2 := by
        intro j hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [hv_eq j hj, mul_pow, inv_pow, div_pow, Real.sq_sqrt hL0.le, Real.sq_sqrt hj0.le]
        dsimp only [a]
        field_simp [hj0.ne', hN0.ne', hL0.ne']
      have hp_sub : Icc 1 N ⊆ Ioc 0 ((N / m + 1) * m) := by
        have hlt : N < (N / m + 1) * m := by
          have hdiv := Nat.div_add_mod N m
          have hmod := Nat.mod_lt N hm
          nlinarith only [hdiv, hmod, Nat.mul_comm m (N / m)]
        intro j hj; simp only [mem_Icc, mem_Ioc] at hj ⊢; omega
      have hsum_periods : ∀ p : ℕ, (∑ j ∈ Ioc 0 (p * m), normalizedRamanujanMode m j ^ 2) =
          (p : ℝ) * m := by
        intro p
        induction p with
        | zero => simp
        | succ p ih =>
          have hu : Ioc 0 ((p + 1) * m) = Ioc 0 (p * m) ∪ Ioc (p * m) (p * m + m) := by
            have : (p + 1) * m = p * m + m := by ring
            rw [this]; ext j; simp only [mem_Ioc, mem_union]; omega
          have hd : Disjoint (Ioc 0 (p * m)) (Ioc (p * m) (p * m + m)) := by
            rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Ioc] at h1 h2; omega
          rw [hu, sum_union hd, ih,
            CompletedArithmeticForms.sum_Ioc_normalizedRamanujanMode_sq hm (p * m)]
          push_cast; ring
      have hsum_mode : (∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2) ≤ 2 * (N : ℝ) := by
        have h1 := sum_le_sum_of_subset_of_nonneg hp_sub fun _ _ _ => sq_nonneg _
        rw [hsum_periods (N / m + 1)] at h1
        have hqm : ((N / m : ℕ) : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
        have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hm_le_N
        push_cast at h1
        linarith only [h1, hqm, hmNR]
      calc
        (∑ j ∈ Icc 1 N, w_v j ^ 2) ≤ ∑ j ∈ Icc 1 N, ((j : ℝ) / N) * v j ^ 2 := sum_le_sum hpt1
        _ = (1 / ((N : ℝ) * Real.log N)) * ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2 := by
          rw [sum_congr rfl hpt2, ← mul_sum]
        _ ≤ (1 / ((N : ℝ) * Real.log N)) * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum_mode (by positivity)
        _ = 2 / Real.log N := by field_simp [hN0.ne', hL0.ne']
    have hpt_rn : ∀ n ∈ Icc 1 N, row_near n ^ 2 ≤ (∑ j ∈ Icc 1 N, W_ker n j * w_v j) ^ 2 := by
      intro n hn
      have h := mul_self_le_mul_self (abs_nonneg _) (hrow_near_le n hn)
      rwa [← sq, sq_abs, ← sq] at h
    calc
      (∑ n ∈ Icc 1 N, row_near n ^ 2) ≤
          ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, W_ker n j * w_v j) ^ 2 := sum_le_sum hpt_rn
      _ ≤ ∑ j ∈ Icc 1 N, B_W ^ 2 * w_v j ^ 2 := hschur
      _ = B_W ^ 2 * ∑ j ∈ Icc 1 N, w_v j ^ 2 := (mul_sum ..).symm
      _ ≤ B_W ^ 2 * (2 / Real.log N) := mul_le_mul_of_nonneg_left hw_sq (sq_nonneg _)
      _ = 128 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N := by
        dsimp only [B_W]; rw [mul_pow, mul_pow, sq_abs]; ring
  have hcol_sq : (∑ n ∈ Icc 1 N, row_col n ^ 2) ≤
      361 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
    have h2 : ∀ n ∈ Icc 1 N, row_col n ^ 2 ≤ 2 * row_far n ^ 2 + 2 * row_near n ^ 2 := fun n _ => by
      have hid : row_col n = row_far n + row_near n := by dsimp only [row_far]; ring
      rw [hid]; nlinarith only [sq_nonneg (row_far n - row_near n)]
    have h1m_sq : 1 ≤ (1 + Real.log m) ^ 2 := by nlinarith only [h1m]
    have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc
      (∑ n ∈ Icc 1 N, row_col n ^ 2) ≤
          2 * (∑ n ∈ Icc 1 N, row_far n ^ 2) + 2 * (∑ n ∈ Icc 1 N, row_near n ^ 2) := by
        refine (sum_le_sum h2).trans_eq ?_; simp only [sum_add_distrib, ← mul_sum]
      _ ≤ 2 * (40 * α ^ 2 / Real.log N) +
            2 * (128 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N) :=
        add_le_add (mul_le_mul_of_nonneg_left hfar_sq zero_le_two)
          (mul_le_mul_of_nonneg_left hnear_sq zero_le_two)
      _ ≤ 361 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N := by
        rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
        exact div_le_div_of_nonneg_right (by nlinarith only [h1m_sq, sq_nonneg α]) hL0.le
      _ ≤ 361 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (sq_nonneg _) hm_ge1) (by positivity))
          hL0.le
  rw [hnorm_eq]
  have h2diff : ∀ n ∈ Icc 1 N,
      (row_pole n - row_col n) ^ 2 ≤ 2 * row_pole n ^ 2 + 2 * row_col n ^ 2 :=
    fun n _ => by nlinarith only [sq_nonneg (row_pole n + row_col n)]
  calc
    (∑ n ∈ Icc 1 N, (row_pole n - row_col n) ^ 2) ≤
        2 * (∑ n ∈ Icc 1 N, row_pole n ^ 2) + 2 * (∑ n ∈ Icc 1 N, row_col n ^ 2) := by
      refine (sum_le_sum h2diff).trans_eq ?_; simp only [sum_add_distrib, ← mul_sum]
    _ ≤ 2 * (10 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N) +
          2 * (361 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N) :=
      add_le_add (mul_le_mul_of_nonneg_left hpole_sq zero_le_two)
        (mul_le_mul_of_nonneg_left hcol_sq zero_le_two)
    _ = 742 * α ^ 2 * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by ring

private theorem norm_eight_signed_sq_le_local {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have h2 : ∀ a b : E, ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := fun a b => by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]
  have h4 : ∀ a b c d : E, ‖a + b + c + d‖ ^ 2 ≤
      4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := fun a b c d => by
    have h := h2 (a + b) (c + d)
    rw [← add_assoc] at h
    linarith only [h, h2 a b, h2 c d]
  have hid : -p + s + c - x + q + (y + z) - u =
      (-p + s + c + -x) + (q + y + z + -u) := by abel
  rw [hid]
  have ha := h2 (-p + s + c + -x) (q + y + z + -u)
  have hb := h4 (-p) s c (-x)
  have hc := h4 q y z (-u)
  rw [norm_neg, norm_neg] at hb
  rw [norm_neg] at hc
  linarith only [ha, hb, hc]

/-- **Sharp `O(m (1 + log m)^2)` complete-Weil conductor residual bound.**
Across every logarithmic conductor range `m ≤ (log N)^A` (`A ≥ 0`), the complete Weil residual of
mode `m` has squared norm `O(m (1 + log m)^2 * rate)` rather than `O(m^4 * rate)`. -/
theorem exists_completeWeil_linear_conductor_residual_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * ((m : ℝ) * (1 + Real.log m) ^ 2) *
            (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
              c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_linear_conductor_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_linear_conductor_bound hφ hsupp hM
  obtain ⟨Cx, hCx, hx⟩ := exists_crossError_linear_conductor_bound hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_linear_conductor_bound hφ hsupp hM
  obtain ⟨Cd, hCd, hdown⟩ := exists_downward_linear_conductor_bound hφ hsupp hM
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenter_linear_conductor_bound φ
  obtain ⟨Cu, hCu, hup⟩ := exists_normalizedUpward_uniform_conductor_variable_rate hφ hsupp hM
  let Cc := 742 * (completeWeilPoleShift φ 1) ^ 2
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + Cd + Cn + Cu) + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall_A : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / (2 * A + 2)) := by
    have hpos : 0 < 1 / (2 * A + 2) := by positivity
    have hsm := tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hpos).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 1] with N hN _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / (2 * A + 2)) := by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
    exact (le_abs_self _).trans habs
  filter_upwards [hup A hA k hk, hsmall_A, eventually_ge_atTop 2, hloglim.eventually_ge_atTop 1]
    with N hupN hLA hN2 hlog
  intro m hm hmL c hc hlarge
  have hN1 : 1 ≤ N := by omega
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := zero_le_one.trans hm1R
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have h1m_sq : 1 ≤ (1 + Real.log (m : ℝ)) ^ 2 := one_le_pow₀ h1m
  let M_log := (m : ℝ) * (1 + Real.log m) ^ 2
  have hMlog0 : 0 ≤ M_log := by dsimp only [M_log]; positivity
  have hm_le_Mlog : (m : ℝ) ≤ M_log := by
    dsimp only [M_log]; exact le_mul_of_one_le_right hm0 h1m_sq
  have hm2_N : m * m ≤ N := by
    have hm_sq : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ (2 * A + 2) := by
      have hp := pow_le_pow_left₀ hm0 hmL 2
      have he : (Real.log (N : ℝ) ^ A) ^ (2 : ℕ) = Real.log (N : ℝ) ^ (2 * A) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
      exact (hp.trans_eq he).trans
        (Real.rpow_le_rpow_of_exponent_le hlog (by linarith only : 2 * A ≤ 2 * A + 2))
    have hL_N : Real.log (N : ℝ) ^ (2 * A + 2) ≤ (N : ℝ) := by
      have hp := Real.rpow_le_rpow hL0.le hLA (by positivity : 0 ≤ 2 * A + 2)
      have he : ((N : ℝ) ^ (1 / (2 * A + 2))) ^ (2 * A + 2) = (N : ℝ) := by
        rw [← Real.rpow_mul hN0.le, one_div_mul_cancel (by positivity), Real.rpow_one]
      exact hp.trans_eq he
    have hcast : ((m * m : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa only [sq, Nat.cast_mul] using hm_sq.trans hL_N
    exact_mod_cast hcast
  let R := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hthree : 3 * c ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 3 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hc2, hlarge]
  have hcN : c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have htwo : 2 * c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have hw : c / N ≤ 1 / 3 := (div_le_iff₀ hN0).mpr (by linarith only [hthree])
  have hrate_div : ∀ {j : ℕ}, j ≤ 5 → c ^ j / Real.log N ≤ R := fun {j} hj => by
    have hcj : c ^ j ≤ c ^ 5 := pow_le_pow_right₀ hc hj
    have h1 : c ^ j / Real.log N ≤ c ^ 5 / Real.log N := div_le_div_of_nonneg_right hcj hL0.le
    dsimp only [R]
    exact h1.trans ((le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity)))
  have hp' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * M_log * R := by
    have h1 : Cp * M_log / Real.log N = Cp * M_log * (c ^ 0 / Real.log N) := by
      rw [pow_zero]; ring
    exact (hp m hm N).trans (h1.trans_le
      (mul_le_mul_of_nonneg_left (hrate_div (by norm_num)) (by positivity)))
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs * M_log * R := by
    have hc210 := pow_le_pow_right₀ hc (by norm_num : 2 ≤ 10)
    have hL2 : 1 ≤ Real.log (N : ℝ) ^ 2 := one_le_pow₀ hlog
    have hscale := mul_le_mul_of_nonneg_left hL2 (pow_nonneg hc0.le 10)
    have hnum : Cs * (m : ℝ) * c ^ 2 ≤
        Cs * M_log * (c ^ 10 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm_le_Mlog hCs.le)
        (hc210.trans (by simpa only [mul_one] using hscale)) (sq_nonneg _) (by positivity)
    calc
      _ ≤ Cs * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 := hs m hm N hN1 hlog c hc0 hcN
      _ ≤ (Cs * M_log * (c ^ 10 * Real.log (N : ℝ) ^ 2)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = Cs * M_log * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by rw [div_pow]; ring
      _ ≤ Cs * M_log * R := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        dsimp only [R]
        have h1 : 0 ≤ c ^ 5 / Real.log N := by positivity
        have h3 : 0 ≤ c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N := by positivity
        linarith only [h1, h3]
  have hc' : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cc * M_log * R := by
    have hcen := fullWeilCenter_residual_linear_conductor_bound (completeWeilPoleShift φ c)
      hm hm2_N hlog
    have hshift : (completeWeilPoleShift φ c) ^ 2 = (completeWeilPoleShift φ 1) ^ 2 * c ^ 2 := by
      unfold completeWeilPoleShift; ring
    have heq : 742 * (completeWeilPoleShift φ c) ^ 2 * M_log / Real.log N =
        Cc * M_log * (c ^ 2 / Real.log N) := by
      dsimp only [Cc]; rw [hshift]; ring
    exact hcen.trans (heq.trans_le
      (mul_le_mul_of_nonneg_left (hrate_div (by norm_num)) (by positivity)))
  have hx' : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ Cx * M_log * R := by
    have hb := hx m hm c hc0 N hN1
    calc
      _ ≤ Cx * (m : ℝ) * c ^ 4 / Real.log N := hb
      _ ≤ Cx * M_log * (c ^ 4 / Real.log N) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le_Mlog hCx) (by positivity)
      _ ≤ Cx * M_log * R := mul_le_mul_of_nonneg_left (hrate_div (by norm_num)) (by positivity)
  have hq' : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ Cq * M_log * R := by
    have hb := hq m hm c hc0 N hN1 hcN
    calc
      _ ≤ Cq * (m : ℝ) * c ^ 4 / Real.log N := hb
      _ ≤ Cq * M_log * (c ^ 4 / Real.log N) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le_Mlog hCq) (by positivity)
      _ ≤ Cq * M_log * R := mul_le_mul_of_nonneg_left (hrate_div (by norm_num)) (by positivity)
  have hd' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      Cd * M_log * R := by
    have hb := hdown m hm c hc N hN1 hw
    calc
      _ ≤ Cd * M_log * (c ^ 5 / Real.log N) := by rw [← mul_div_assoc]; exact hb
      _ ≤ Cd * M_log * R := mul_le_mul_of_nonneg_left (hrate_div (by norm_num)) (by positivity)
  have hn' : ‖nearCenterVector φ c N m‖ ^ 2 ≤ Cn * M_log * R := by
    have hb := hnear m hm c hc N hN1 htwo
    calc
      _ ≤ Cn * (m : ℝ) * c ^ 5 / Real.log N := hb
      _ ≤ Cn * M_log * (c ^ 5 / Real.log N) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le_Mlog hCn) (by positivity)
      _ ≤ Cn * M_log * R := mul_le_mul_of_nonneg_left (hrate_div (by norm_num)) (by positivity)
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cu * M_log * R := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    have htot_le : (m.totient : ℝ) ≤ M_log :=
      (by exact_mod_cast Nat.totient_le m : (m.totient : ℝ) ≤ m).trans hm_le_Mlog
    calc
      (m.totient : ℝ)⁻¹ * ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤
          (m.totient : ℝ)⁻¹ * (Cu * (m.totient : ℝ) ^ 2 * R) :=
        mul_le_mul_of_nonneg_left (hupN m hm hmL c hc hlarge) (by positivity)
      _ = Cu * (m.totient : ℝ) * R := by field_simp [htot_pos.ne']
      _ ≤ Cu * M_log * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htot_le hCu.le) hR0
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm]
  have hsum := norm_eight_signed_sq_le_local
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  have hb := hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hp' hs') hc') hx') hq') hd') hn') hu')
    (by norm_num : (0 : ℝ) ≤ 8))
  calc
    _ ≤ 8 * (Cp * M_log * R + Cs * M_log * R + Cc * M_log * R + Cx * M_log * R +
          Cq * M_log * R + Cd * M_log * R + Cn * M_log * R + Cu * M_log * R) := hb
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + Cd + Cn + Cu)) * M_log * R := by ring
    _ ≤ K * M_log * R :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only) hMlog0) hR0

/-- Specialization of `exists_completeWeil_linear_conductor_residual_variable_rate` to `tiltedUnitSpline`. -/
theorem exists_tiltedUnitSpline_linear_conductor_residual_variable_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * ((m : ℝ) * (1 + Real.log m) ^ 2) *
            (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
              c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) :=
  exists_completeWeil_linear_conductor_residual_variable_rate contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

/-! ## Section 3: Defect-Localized Prime Cross-Pairing and Sharpened Power-Log Positivity -/

/-- Sharpened unconditional power-of-logarithm overlap positivity exponent `2 / 71`. -/
def sharpenedPowerLogExponent : ℝ :=
  2 / 71

theorem sharpenedPowerLogExponent_pos : 0 < sharpenedPowerLogExponent := by
  norm_num [sharpenedPowerLogExponent]

theorem powerLogPositivityExponent_lt_sharpened :
    powerLogPositivityExponent < sharpenedPowerLogExponent := by
  norm_num [powerLogPositivityExponent, sharpenedPowerLogExponent]

theorem one_div_36_lt_sharpened :
    (1 / 36 : ℝ) < sharpenedPowerLogExponent := by
  norm_num [sharpenedPowerLogExponent]

/-- **Defect-localized prime cross-pairing between `conductorSubspace R' N` and its orthogonal
complement.** Splitting `Icc 1 N = Icc 1 (N / R'^4) ∪ Ioc (N / R'^4) N` bounds the deep residual of
`u ∈ conductorSubspace R' N` by `O(1) ‖u‖` and pairs the top-strip residual against the
`poleDefect`-controlled top-strip mass of `w ∈ (conductorSubspace R' N)ᗮ`, saving a factor of
`√(log N)` on the `(1 + log R')^2` top-strip contribution. -/
private theorem exists_fullPrimeMatrix_orthog_inner_defect_localized :
    ∃ C_bulk C_def : ℝ, 1 ≤ C_bulk ∧ 1 ≤ C_def ∧
      ∀ {R' N : ℕ}, 2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
      ∀ {u w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → w ∈ (conductorSubspace R' N)ᗮ →
        |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
          C_bulk * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) *
            ‖u‖ * ‖w‖ +
          C_def * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) *
            ‖u‖ * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by
  obtain ⟨C_env, hC_env_pos, hC_env⟩ :=
    SignedArithmeticHodgeTheory.exists_primeMertensRemainder_log_envelope
  obtain ⟨C_res, hC_res_pos, hpr_res⟩ :=
    CompletedArithmeticForms.exists_fullPrimeMatrix_packet_residual_norm_le
  let C_deep := Real.sqrt (2 * C_env ^ 2 + 128) + 1
  let C_bulk := C_deep + 7 * C_res + 1
  let C_def := 2 * C_res + 1
  refine ⟨C_bulk, C_def, by dsimp only [C_bulk, C_deep]; positivity,
    by dsimp only [C_def]; positivity, ?_⟩
  intro R' N hR' hR6N hlog u w hu hw
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R') (N := N) (x := u)).mp hu
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hL1 : 1 ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have h1R : 1 ≤ 1 + Real.log (R' : ℝ) := by
    have := Real.log_natCast_nonneg R'; linarith only [this]
  have hriesz_a : (∑ m ∈ Icc 1 R', a m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    have h := (half_and_three_halves_riesz_of_log_le hR' hRR_N hlog a).1
    rw [← hu_eq] at h
    linarith only [h]
  let diagVec := ∑ m ∈ Icc 1 R',
    (a m * (Real.log N - ramanujanAdjunctionEnergy m)) • normalizedRamanujanHorizonVector m N
  have hd_mem : diagVec ∈ conductorSubspace R' N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R' N _
  have hd_orth : ⟪diagVec, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hd_mem hw
  let resVec := Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec
  have hinner_eq : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ = ⟪resVec, w⟫ := by
    dsimp only [resVec]; rw [inner_sub_left, hd_orth, sub_zero]
  let K := N / R' ^ 4
  have hR4_pos : 0 < R' ^ 4 := pow_pos (by omega) 4
  have hRR_K : R' * R' ≤ K := (Nat.le_div_iff_mul_le hR4_pos).mpr
    (by calc R' * R' * R' ^ 4 = R' ^ 6 := by ring
             _ ≤ N := hR6N)
  have hK4 : 4 ≤ K := (Nat.mul_le_mul hR' hR').trans hRR_K
  have hK1 : 1 ≤ K := by omega
  have hKN : K ≤ N := Nat.div_le_self N (R' ^ 4)
  have hN1 : 1 ≤ N := hK1.trans hKN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hsplit_Icc : Icc 1 N = Icc 1 K ∪ Ioc K N := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj_Icc : Disjoint (Icc 1 K) (Ioc K N) := by
    rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  have hdot_split : ⟪resVec, w⟫ =
      (∑ n ∈ Icc 1 K, primeHorizonExtension resVec n * primeHorizonExtension w n) +
      (∑ n ∈ Ioc K N, primeHorizonExtension resVec n * primeHorizonExtension w n) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ idx : PrimeHorizonIndex N, w.ofLp idx * resVec.ofLp idx) = _
    have heq : (∑ idx : PrimeHorizonIndex N, w.ofLp idx * resVec.ofLp idx) =
        ∑ n ∈ Icc 1 N, primeHorizonExtension resVec n * primeHorizonExtension w n := by
      rw [← sum_coe_sort (Icc 1 N)]
      exact sum_congr rfl fun idx _ => by
        rw [primeHorizonExtension_coe resVec idx, primeHorizonExtension_coe w idx]
        exact mul_comm _ _
    rw [heq, hsplit_Icc, sum_union hdisj_Icc]
  -- 1. Deep region `Icc 1 K` (`1 ≤ n ≤ N / R'^4`): `∑_{n=1}^K resVec(n)^2 ≤ (2 C_env^2 + 128) ‖u‖^2`.
  have hdeep_sq : (∑ n ∈ Icc 1 K, primeHorizonExtension resVec n ^ 2) ≤
      (2 * C_env ^ 2 + 128) * ‖u‖ ^ 2 := by
    let e_mert : ℕ → ℝ := fun y => mertensSum y - Real.log y + Real.eulerMascheroniConstant
    let r_round : ℕ → ℝ := fun n => Real.log N - Real.log ((N / n : ℕ) : ℝ) - Real.log n
    let corr_term : ℕ → ℝ := fun n => poleVector n * ∑ m ∈ Icc 1 R',
      a m * (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
        (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)
    have hres_coord : ∀ n ∈ Icc 1 N, primeHorizonExtension resVec n =
        (e_mert (N / n) - r_round n) * primeHorizonExtension u n +
          (Real.sqrt (Real.log N))⁻¹ * corr_term n := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      have hcoord : primeHorizonExtension resVec n =
          (Real.sqrt (Real.log N))⁻¹ * ∑ m ∈ Icc 1 R', a m * ramanujanPrimeResidual m N n := by
        rw [primeHorizonExtension_coe resVec ⟨n, hn⟩]
        change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩) resVec = _
        dsimp only [resVec, diagVec]
        rw [hu_eq, map_sub, map_sum, map_sum, map_sum, ← sum_sub_distrib, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [map_smul, map_smul, map_smul]
        change a m * (Matrix.toEuclideanLin (fullPrimeMatrix N)
            (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩) -
          a m * (Real.log N - ramanujanAdjunctionEnergy m) *
            normalizedRamanujanHorizonVector m N ⟨n, hn⟩ = _
        dsimp only [normalizedRamanujanHorizonVector]
        rw [map_smul]
        change a m * ((Real.sqrt (Real.log N))⁻¹ *
            Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) ⟨n, hn⟩) -
          a m * (Real.log N - ramanujanAdjunctionEnergy m) *
            ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
        rw [fullPrimeMatrix_apply_ramanujanHorizonVector, ramanujanPrimeResidual]
        ring
      have hu_apply : (Real.sqrt (Real.log N))⁻¹ * poleVector n *
          (∑ m ∈ Icc 1 R', a m * normalizedRamanujanMode m n) = primeHorizonExtension u n := by
        rw [primeHorizonExtension_coe u ⟨n, hn⟩]
        change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩) u
        rw [hu_eq, map_sum, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        change (Real.sqrt (Real.log N))⁻¹ * poleVector n * (a m * normalizedRamanujanMode m n) =
          a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n)
        rw [ramanujanPoleProfile_eq_mul_poleVector]
        ring
      have hid_m : ∀ m ∈ Icc 1 R', ramanujanPrimeResidual m N n =
          ((e_mert (N / n) - r_round n) * normalizedRamanujanMode m n +
            (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
              (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) * poleVector n := by
        intro m _
        rw [ramanujanPrimeResidual]
        simp only [ramanujanPoleProfile_eq_mul_poleVector]
        rw [sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m) hn1 hnN]
        dsimp only [e_mert, r_round, ramanujanAdjunctionEnergy]
        ring
      rw [hcoord, sum_congr rfl (fun m hm => by rw [hid_m m hm])]
      have hsum_m : (∑ m ∈ Icc 1 R', a m *
          (((e_mert (N / n) - r_round n) * normalizedRamanujanMode m n +
            (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
              (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) * poleVector n)) =
          (e_mert (N / n) - r_round n) * poleVector n *
            (∑ m ∈ Icc 1 R', a m * normalizedRamanujanMode m n) + corr_term n := by
        dsimp only [corr_term]
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun m _ => by ring
      rw [hsum_m, mul_add, ← hu_apply]
      ring
    have hmert_K : (∑ n ∈ Icc 1 K, ((e_mert (N / n) - r_round n) * primeHorizonExtension u n) ^ 2) ≤
        C_env ^ 2 * ‖u‖ ^ 2 := by
      have hsub : Icc 1 K ⊆ Icc 1 N := Icc_subset_Icc le_rfl hKN
      have hpt : ∀ n ∈ Icc 1 N,
          ((e_mert (N / n) - r_round n) * primeHorizonExtension u n) ^ 2 ≤
            C_env ^ 2 * primeHorizonExtension u n ^ 2 := by
        intro n hn
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        have hy1 : 1 ≤ N / n := Nat.div_pos hnN hn1
        have hr_bd := roundoff_le hn1 hnN
        have her_abs : |e_mert (N / n) - r_round n| ≤ C_env := by
          have h1 : |e_mert (N / n) - r_round n| ≤
              SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) := by
            unfold SignedArithmeticHodgeTheory.primeMertensRemainderProfile
            calc
              |e_mert (N / n) - r_round n| ≤ |e_mert (N / n)| + |r_round n| := abs_sub _ _
              _ ≤ |e_mert (N / n)| + 1 / ((N / n : ℕ) : ℝ) := by
                rw [abs_of_nonneg hr_bd.1]; exact add_le_add le_rfl hr_bd.2
          have hden : 1 ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
            have := Real.log_natCast_nonneg (N / n); linarith
          exact h1.trans ((hC_env (N / n) hy1).trans (div_le_self hC_env_pos.le hden))
        have her_sq : (e_mert (N / n) - r_round n) ^ 2 ≤ C_env ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) her_abs 2
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right her_sq (sq_nonneg _)
      calc
        (∑ n ∈ Icc 1 K, ((e_mert (N / n) - r_round n) * primeHorizonExtension u n) ^ 2) ≤
            ∑ n ∈ Icc 1 N, ((e_mert (N / n) - r_round n) * primeHorizonExtension u n) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
        _ ≤ ∑ n ∈ Icc 1 N, C_env ^ 2 * primeHorizonExtension u n ^ 2 := sum_le_sum hpt
        _ = C_env ^ 2 * ‖u‖ ^ 2 := by rw [← mul_sum, sum_primeHorizonExtension_sq]
    have hcorr_K : (Real.log N)⁻¹ * (∑ n ∈ Icc 1 K, corr_term n ^ 2) ≤ 64 * ‖u‖ ^ 2 := by
      have ha_l1_sq : (∑ m ∈ Icc 1 R', |a m|) ^ 2 ≤ (R' : ℝ) * ∑ m ∈ Icc 1 R', a m ^ 2 := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R') (fun _ => (1 : ℝ)) (fun m => |a m|)
        simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
          Nat.add_sub_cancel, sq_abs] at hcs
        exact hcs
      have hR0 : (0 : ℝ) < R' := by exact_mod_cast (show 0 < R' by omega)
      have hpt_corr : ∀ n ∈ Icc 1 K, corr_term n ^ 2 ≤
          16 * (1 / (n : ℝ)) * ∑ m ∈ Icc 1 R', a m ^ 2 := by
        intro n hn
        obtain ⟨hn1, hnK⟩ := mem_Icc.mp hn
        have hn_pos : 0 < n := hn1
        have hy_ge : R' ^ 4 ≤ N / n := (Nat.le_div_iff_mul_le hn_pos).mpr
          ((Nat.mul_comm n (R' ^ 4)).trans_le (Nat.mul_le_of_le_div (R' ^ 4) n N hnK))
        have hy_pos : 0 < N / n := lt_of_lt_of_le hR4_pos hy_ge
        have hyR : (R' : ℝ) ^ 4 ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hy_ge
        have hm_bd : ∀ m ∈ Icc 1 R',
            |poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
              (Real.log m + tameDifferent m) * normalizedRamanujanMode m n| ≤
              4 / (R' : ℝ) ^ 2 := by
          intro m hm
          obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
          have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
          have hc_le := SignedArithmeticHodgeTheory.abs_normalizedRamanujan_correction_le
            hm1 hn_pos hy_pos
          have htot_R : Real.sqrt (m.totient : ℝ) ≤ R' := by
            have h1 : (m.totient : ℝ) ≤ R' :=
              (by exact_mod_cast Nat.totient_le m : (m.totient : ℝ) ≤ m).trans
                (by exact_mod_cast hmR)
            have hR1 : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
            exact (Real.sqrt_le_sqrt h1).trans
              ((Real.sqrt_le_sqrt (by nlinarith only [hR1] : (R' : ℝ) ≤ (R' : ℝ) ^ 2)).trans_eq
                (Real.sqrt_sq hR0.le))
          have hlog_R : Real.log (m : ℝ) ≤ R' :=
            ((Real.log_le_sub_one_of_pos hm0).trans (by linarith only)).trans
              (by exact_mod_cast hmR)
          calc
            _ ≤ 4 * Real.sqrt (m.totient : ℝ) * Real.log m / ((N / n : ℕ) : ℝ) := hc_le
            _ ≤ 4 * (R' : ℝ) * (R' : ℝ) / (R' : ℝ) ^ 4 := by
              refine div_le_div₀ (by positivity) ?_ (by positivity) hyR
              exact mul_le_mul (mul_le_mul_of_nonneg_left htot_R (by norm_num)) hlog_R
                (Real.log_natCast_nonneg m) (by positivity)
            _ = 4 / (R' : ℝ) ^ 2 := by field_simp [hR0.ne']; ring
        have habs_corr : |corr_term n| ≤ poleVector n * (4 / (R' : ℝ) ^ 2) * ∑ m ∈ Icc 1 R', |a m| := by
          dsimp only [corr_term]
          have hp0 : 0 ≤ poleVector n := by unfold poleVector; positivity
          rw [abs_mul, abs_of_nonneg hp0, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hp0
          calc
            |∑ m ∈ Icc 1 R', a m * _| ≤
                ∑ m ∈ Icc 1 R', |a m| * (4 / (R' : ℝ) ^ 2) := by
              refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hm_bd m hm) (abs_nonneg _)
            _ = (4 / (R' : ℝ) ^ 2) * ∑ m ∈ Icc 1 R', |a m| := by rw [← sum_mul, mul_comm]
        have hsq_corr := mul_self_le_mul_self (abs_nonneg _) habs_corr
        rw [← sq, sq_abs, ← sq, mul_pow, mul_pow, poleVector_sq] at hsq_corr
        have hR1 : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
        have hR3 : (1 : ℝ) ≤ (R' : ℝ) ^ 3 := one_le_pow₀ hR1
        calc
          corr_term n ^ 2 ≤ (1 / (n : ℝ)) * (4 / (R' : ℝ) ^ 2) ^ 2 *
              ((R' : ℝ) * ∑ m ∈ Icc 1 R', a m ^ 2) :=
            hsq_corr.trans (mul_le_mul_of_nonneg_left ha_l1_sq (by positivity))
          _ = 16 * (1 / (n : ℝ)) * (∑ m ∈ Icc 1 R', a m ^ 2) / (R' : ℝ) ^ 3 := by
            field_simp [hR0.ne']; ring
          _ ≤ 16 * (1 / (n : ℝ)) * ∑ m ∈ Icc 1 R', a m ^ 2 :=
            div_le_self (mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)) hR3
      have hhar_K : (∑ n ∈ Icc 1 K, (1 / (n : ℝ))) ≤ 2 * Real.log N := by
        have h1 := _root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log K
        have hlogK : Real.log (K : ℝ) ≤ Real.log N := Real.log_le_log hK0 (by exact_mod_cast hKN)
        linarith only [h1, hlogK, hL1]
      calc
        (Real.log N)⁻¹ * (∑ n ∈ Icc 1 K, corr_term n ^ 2) ≤
            (Real.log N)⁻¹ * ∑ n ∈ Icc 1 K, 16 * (1 / (n : ℝ)) * ∑ m ∈ Icc 1 R', a m ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum hpt_corr) (inv_nonneg.mpr hL0.le)
        _ = (Real.log N)⁻¹ * (16 * (∑ n ∈ Icc 1 K, (1 / (n : ℝ))) * ∑ m ∈ Icc 1 R', a m ^ 2) := by
          congr 1; simp only [← mul_sum, ← sum_mul]; ring
        _ ≤ (Real.log N)⁻¹ * (16 * (2 * Real.log N) * (2 * ‖u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_left hhar_K (by norm_num)) hriesz_a
              (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
            (inv_nonneg.mpr hL0.le)
        _ = 64 * ‖u‖ ^ 2 := by field_simp [hL0.ne']; ring
    have hpt_2 : ∀ n ∈ Icc 1 K, primeHorizonExtension resVec n ^ 2 ≤
        2 * ((e_mert (N / n) - r_round n) * primeHorizonExtension u n) ^ 2 +
          2 * ((Real.log N)⁻¹ * corr_term n ^ 2) := by
      intro n hn
      rw [hres_coord n (Icc_subset_Icc le_rfl hKN hn)]
      have hsq : ((Real.sqrt (Real.log N))⁻¹ * corr_term n) ^ 2 =
          (Real.log N)⁻¹ * corr_term n ^ 2 := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hL0.le]
      nlinarith only [hsq,
        sq_nonneg ((e_mert (N / n) - r_round n) * primeHorizonExtension u n -
          (Real.sqrt (Real.log N))⁻¹ * corr_term n)]
    calc
      (∑ n ∈ Icc 1 K, primeHorizonExtension resVec n ^ 2) ≤
          2 * (∑ n ∈ Icc 1 K, ((e_mert (N / n) - r_round n) * primeHorizonExtension u n) ^ 2) +
            2 * ((Real.log N)⁻¹ * ∑ n ∈ Icc 1 K, corr_term n ^ 2) := by
        refine (sum_le_sum hpt_2).trans_eq ?_
        simp only [sum_add_distrib, ← mul_sum]; ring
      _ ≤ 2 * (C_env ^ 2 * ‖u‖ ^ 2) + 2 * (64 * ‖u‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hmert_K zero_le_two)
          (mul_le_mul_of_nonneg_left hcorr_K zero_le_two)
      _ = (2 * C_env ^ 2 + 128) * ‖u‖ ^ 2 := by ring
  have hdeep_inner : |∑ n ∈ Icc 1 K, primeHorizonExtension resVec n * primeHorizonExtension w n| ≤
      C_deep * ‖u‖ * ‖w‖ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 K)
      (primeHorizonExtension resVec) (primeHorizonExtension w)
    have hw_K : (∑ n ∈ Icc 1 K, primeHorizonExtension w n ^ 2) ≤ ‖w‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq w]
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hKN) fun _ _ _ => sq_nonneg _
    have hcd_sq : 2 * C_env ^ 2 + 128 ≤ C_deep ^ 2 := by
      dsimp only [C_deep]
      have h0 : 0 ≤ Real.sqrt (2 * C_env ^ 2 + 128) := Real.sqrt_nonneg _
      have hsq : Real.sqrt (2 * C_env ^ 2 + 128) ^ 2 = 2 * C_env ^ 2 + 128 :=
        Real.sq_sqrt (by positivity)
      nlinarith only [h0, hsq]
    have hsq : (∑ n ∈ Icc 1 K, primeHorizonExtension resVec n * primeHorizonExtension w n) ^ 2 ≤
        (C_deep * ‖u‖ * ‖w‖) ^ 2 := by
      calc
        _ ≤ (∑ n ∈ Icc 1 K, primeHorizonExtension resVec n ^ 2) *
              (∑ n ∈ Icc 1 K, primeHorizonExtension w n ^ 2) := hcs
        _ ≤ ((2 * C_env ^ 2 + 128) * ‖u‖ ^ 2) * ‖w‖ ^ 2 :=
          mul_le_mul hdeep_sq hw_K (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ ≤ (C_deep ^ 2 * ‖u‖ ^ 2) * ‖w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd_sq (sq_nonneg _)) (sq_nonneg _)
        _ = (C_deep * ‖u‖ * ‖w‖) ^ 2 := by ring
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by dsimp only [C_deep]; positivity))
  -- 2. Top strip `Ioc K N`: bound `resVec` by full packet residual norm, and `w` by `poleDefect`.
  have htop_res_sq : (∑ n ∈ Ioc K N, primeHorizonExtension resVec n ^ 2) ≤
      (C_res * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖) ^ 2 := by
    have hsub : Ioc K N ⊆ Icc 1 N := fun n hn => by
      simp only [mem_Ioc, mem_Icc] at hn ⊢; omega
    have h1 := sum_le_sum_of_subset_of_nonneg hsub (f := fun n => primeHorizonExtension resVec n ^ 2)
      (fun _ _ _ => sq_nonneg _)
    rw [sum_primeHorizonExtension_sq resVec] at h1
    have hnorm := hpr_res hR' hR6N hlog a
    rw [← hu_eq] at hnorm
    have hsq := pow_le_pow_left₀ (norm_nonneg resVec) hnorm 2
    exact h1.trans hsq
  have htop_w_sq : (∑ n ∈ Ioc K N, primeHorizonExtension w n ^ 2) ≤
      ((2 / Real.sqrt (Real.log N)) * Real.sqrt (poleDefect N (primeHorizonExtension w)) +
        (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖w‖) ^ 2 := by
    have htail_eq : (∑ n ∈ Ioc K N, primeHorizonExtension w n ^ 2) =
        ∑ n ∈ Icc 1 N, atomicTailCoefficients K (primeHorizonExtension w) n ^ 2 := by
      simp_rw [atomicTailCoefficients_sq]
      rw [← sum_filter]
      congr 1
      ext n; simp only [mem_Ioc, mem_filter, mem_Icc]; omega
    have hdef := log_mul_tail_mass_le_defect hK1 hKN (primeHorizonExtension w) zero_lt_one
    rw [← htail_eq, sum_primeHorizonExtension_sq w,
      show (1 + 1 / (1 : ℝ)) = 2 by norm_num, show (1 + (1 : ℝ)) = 2 by norm_num] at hdef
    have hlogNK : Real.log N - Real.log K ≤ 8 * Real.log R' := by
      have hN_le : (N : ℝ) ≤ 2 * (K : ℝ) * (R' : ℝ) ^ 4 := by
        have hdiv := Nat.div_add_mod N (R' ^ 4)
        have hmod : N % R' ^ 4 < R' ^ 4 := Nat.mod_lt N hR4_pos
        have hnat : N ≤ (K + 1) * R' ^ 4 := by
          dsimp only [K]; nlinarith only [hdiv, hmod, Nat.mul_comm (R' ^ 4) (N / R' ^ 4)]
        have hK1_le : K + 1 ≤ 2 * K := by omega
        exact_mod_cast hnat.trans (Nat.mul_le_mul_right (R' ^ 4) hK1_le)
      have hR0 : (0 : ℝ) < R' := by exact_mod_cast (show 0 < R' by omega)
      have hlog1 := Real.log_le_log hN0 hN_le
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul two_ne_zero hK0.ne',
        Real.log_pow] at hlog1
      have hlog2_R : Real.log 2 ≤ Real.log R' :=
        Real.log_le_log zero_lt_two (by exact_mod_cast hR')
      have hlogR0 : 0 ≤ Real.log (R' : ℝ) := Real.log_natCast_nonneg R'
      linarith only [hlog1, hlog2_R, hlogR0]
    have hcost_le : 2 * cutoffPrimeCost K N + Real.log N - Real.log K ≤
        49 * (1 + Real.log R') := by
      unfold cutoffPrimeCost
      have hlog4 : Real.log 4 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        linarith only [this, h4]
      have hlog8 : Real.log 8 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        have h8 : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
        linarith only [this, h8]
      have hlogR0 : 0 ≤ Real.log (R' : ℝ) := Real.log_natCast_nonneg R'
      linarith only [hlogNK, hlog4, hlog8, hlogR0]
    have hdiv := (le_div_iff₀' hL0).mpr hdef
    have hbound1 : (∑ n ∈ Ioc K N, primeHorizonExtension w n ^ 2) ≤
        (2 / Real.log N) * poleDefect N (primeHorizonExtension w) +
          (49 * (1 + Real.log R') / Real.log N) * ‖w‖ ^ 2 := by
      calc
        _ ≤ (2 * poleDefect N (primeHorizonExtension w) +
              (2 * cutoffPrimeCost K N + Real.log N - Real.log K) * ‖w‖ ^ 2) / Real.log N := hdiv
        _ ≤ (2 * poleDefect N (primeHorizonExtension w) +
              49 * (1 + Real.log R') * ‖w‖ ^ 2) / Real.log N :=
          div_le_div_of_nonneg_right
            (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcost_le (sq_nonneg _))) hL0.le
        _ = (2 / Real.log N) * poleDefect N (primeHorizonExtension w) +
              (49 * (1 + Real.log R') / Real.log N) * ‖w‖ ^ 2 := by ring
    let A_w := (2 / Real.sqrt (Real.log N)) * Real.sqrt (poleDefect N (primeHorizonExtension w))
    let B_w := (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖w‖
    have hAw0 : 0 ≤ A_w := by dsimp only [A_w]; positivity
    have hBw0 : 0 ≤ B_w := by dsimp only [B_w]; positivity
    have hAw_sq : (2 / Real.log N) * poleDefect N (primeHorizonExtension w) ≤ A_w ^ 2 := by
      dsimp only [A_w]
      rw [mul_pow, div_pow, Real.sq_sqrt hL0.le,
        Real.sq_sqrt (poleDefect_nonneg N (primeHorizonExtension w))]
      have hd0 := poleDefect_nonneg N (primeHorizonExtension w)
      have : 2 / Real.log N ≤ 4 / Real.log N :=
        div_le_div_of_nonneg_right (by norm_num) hL0.le
      exact mul_le_mul_of_nonneg_right this hd0
    have hBw_sq : (49 * (1 + Real.log R') / Real.log N) * ‖w‖ ^ 2 = B_w ^ 2 := by
      dsimp only [B_w]
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by linarith only [h1R]), Real.sq_sqrt hL0.le]
      ring
    calc
      (∑ n ∈ Ioc K N, primeHorizonExtension w n ^ 2) ≤ A_w ^ 2 + B_w ^ 2 :=
        hbound1.trans (add_le_add hAw_sq hBw_sq.le)
      _ ≤ (A_w + B_w) ^ 2 := by nlinarith only [hAw0, hBw0]
  have htop_inner : |∑ n ∈ Ioc K N, primeHorizonExtension resVec n * primeHorizonExtension w n| ≤
      (C_res * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖) *
        ((2 / Real.sqrt (Real.log N)) * Real.sqrt (poleDefect N (primeHorizonExtension w)) +
          (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖w‖) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Ioc K N)
      (primeHorizonExtension resVec) (primeHorizonExtension w)
    let X_r := C_res * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖
    let Y_w := (2 / Real.sqrt (Real.log N)) * Real.sqrt (poleDefect N (primeHorizonExtension w)) +
      (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖w‖
    have hXr0 : 0 ≤ X_r := by dsimp only [X_r]; positivity
    have hYw0 : 0 ≤ Y_w := by dsimp only [Y_w]; positivity
    have hsq : (∑ n ∈ Ioc K N, primeHorizonExtension resVec n * primeHorizonExtension w n) ^ 2 ≤
        (X_r * Y_w) ^ 2 := by
      calc
        _ ≤ (∑ n ∈ Ioc K N, primeHorizonExtension resVec n ^ 2) *
              (∑ n ∈ Ioc K N, primeHorizonExtension w n ^ 2) := hcs
        _ ≤ X_r ^ 2 * Y_w ^ 2 :=
          mul_le_mul htop_res_sq htop_w_sq (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ = (X_r * Y_w) ^ 2 := (mul_pow X_r Y_w 2).symm
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (mul_nonneg hXr0 hYw0))
  -- Combine deep + top bounds cleanly.
  have h1R_sqrt_L : Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 := by
    have h1 : 1 + Real.log (R' : ℝ) ≤ Real.log N := by linarith only [hlog, h1R]
    exact (div_le_one (Real.sqrt_pos.mpr hL0)).mpr (Real.sqrt_le_sqrt h1)
  have hsL_pos : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have htop_expand :
      (C_res * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖) *
        ((2 / Real.sqrt (Real.log N)) * Real.sqrt (poleDefect N (primeHorizonExtension w)) +
          (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖w‖) ≤
      7 * C_res * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) *
        ‖u‖ * ‖w‖ +
      2 * C_res * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) *
        ‖u‖ * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by
    have hb_part :
        (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) *
          (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) ≤
        7 * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) := by
      have hprod : ((1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) *
          (Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) =
          (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N := by
        rw [div_mul_div_comm, Real.mul_self_sqrt hL0.le]
      calc
        (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) *
            (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) =
            7 * (Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) +
              7 * (((1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) *
                (Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N))) := by ring
        _ ≤ 7 * 1 + 7 * ((1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) := by
          rw [hprod]; linarith only [h1R_sqrt_L]
        _ = _ := by ring
    have hd_part :
        (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * (2 / Real.sqrt (Real.log N)) =
        2 * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) := by
      have hsq_sL : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
        Real.mul_self_sqrt hL0.le
      calc
        (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * (2 / Real.sqrt (Real.log N)) =
            2 * (1 / Real.sqrt (Real.log N) +
              (1 + Real.log R') ^ 2 / (Real.sqrt (Real.log N) * Real.sqrt (Real.log N))) := by
          field_simp [hsL_pos.ne']
        _ = 2 * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) := by
          rw [hsq_sL]
    have hmul_b := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb_part hC_res_pos.le) (norm_nonneg u))
      (norm_nonneg w)
    rw [mul_add]
    have h1_eq : (C_res * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖) *
        ((2 / Real.sqrt (Real.log N)) * Real.sqrt (poleDefect N (primeHorizonExtension w))) =
        2 * C_res * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) *
          ‖u‖ * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by
      calc
        _ = C_res * ((1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) *
              (2 / Real.sqrt (Real.log N))) * ‖u‖ *
              Real.sqrt (poleDefect N (primeHorizonExtension w)) := by ring
        _ = _ := by rw [hd_part]; ring
    have h2_eq : (C_res * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖) *
        ((7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖w‖) =
        C_res * ((1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) *
          (7 * Real.sqrt (1 + Real.log R') / Real.sqrt (Real.log N))) * ‖u‖ * ‖w‖ := by ring
    rw [h1_eq, h2_eq]
    linarith only [hmul_b, (by ring :
      C_res * (7 * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N)) *
        ‖u‖ * ‖w‖ =
      7 * C_res * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) *
        ‖u‖ * ‖w‖)]
  rw [hinner_eq, hdot_split]
  have htri := abs_add_le
    (∑ n ∈ Icc 1 K, primeHorizonExtension resVec n * primeHorizonExtension w n)
    (∑ n ∈ Ioc K N, primeHorizonExtension resVec n * primeHorizonExtension w n)
  have hdeep_up : C_deep * ‖u‖ * ‖w‖ ≤
      C_deep * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) *
        ‖u‖ * ‖w‖ := by
    have hpos : 0 ≤ (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N := by
      positivity
    have h1 : C_deep ≤
        C_deep * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) :=
      le_mul_of_one_le_right (by dsimp only [C_deep]; positivity) (by linarith only [hpos])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg u)) (norm_nonneg w)
  have h1_nonneg : 0 ≤ (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) *
      ‖u‖ * ‖w‖ := by positivity
  have h2_nonneg : 0 ≤ (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) *
      ‖u‖ * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by positivity
  dsimp only [C_bulk, C_def]
  linarith only [htri, hdeep_inner, hdeep_up, htop_inner, htop_expand, h1_nonneg, h2_nonneg]

/-- **Defect-localized complete-Weil orthogonal cross-pairing.**
Replaces the `(1 + log R')^2 / √(log N) ≤ c^3` ceiling in `exists_completeWeilMatrix_orthog_cross_le`
with `(1 + log R')^5 / (log N)^2 ≤ c^9` plus a `poleDefect`-weighted top-strip cross term, removing
the `1 / 58` prime cross-pairing cap completely. -/
private theorem exists_completeWeilMatrix_orthog_cross_defect_localized :
    ∃ C_cross C_pdef : ℝ, 1 ≤ C_cross ∧ 1 ≤ C_pdef ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 →
        (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N ≤
          c ^ 4 * Real.sqrt c →
        (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ 1 →
      ∀ {u w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ →
        w ∈ (conductorSubspace R' N)ᗮ →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
          C_cross * (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ +
          C_pdef * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) *
            ‖u‖ * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by
  obtain ⟨C_bulk, C_def, hC_bulk, hC_def, hpr⟩ :=
    exists_fullPrimeMatrix_orthog_inner_defect_localized
  obtain ⟨C_od, hC_od, hod⟩ :=
    CompletedArithmeticForms.exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_up, hC_up, hup⟩ :=
    CompletedArithmeticForms.exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep := 4 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep0 : 0 ≤ C_sep := by
    have := integral_tiltedUnitSpline_sq_pos; dsimp only [C_sep]; positivity
  let C_cross := 2 * C_bulk + 144 + C_sep + 3 * C_od + 2 * C_up + 1
  refine ⟨C_cross, C_def, by dsimp only [C_cross]; linarith [hC_bulk, hC_od, hC_up, hC_sep0],
    hC_def, ?_⟩
  intro R' N c hR' hR6N hlog hc1 hw1 hRNT_lin hRNT_up hlog_div1 hlog_div25 hR_sqrt
    u w hu hu1 hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hN2 : 2 ≤ N := by have := Nat.mul_le_mul hR' hR'; omega
  have hN1 : 1 ≤ N := by omega
  have hw1_orth : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R') N hv)
  have huw_orth : ⟪u, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hw
  have hsqrt_1lc : Real.sqrt (1 + Real.log c) ≤ 2 * c := by
    have h1lc_le : 1 + Real.log c ≤ 2 * c := by
      have hlc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
      linarith only [hlc, hc1]
    exact (Real.sqrt_le_sqrt (h1lc_le.trans (by nlinarith only [hc1]))).trans_eq
      (Real.sqrt_sq (by positivity))
  have hc13 : c ≤ c ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 3)
  have hc23 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 3)
  have h1_c3 : 1 ≤ c ^ 3 := one_le_pow₀ hc1
  have hc3_Sc : c ^ 3 ≤ c ^ 4 * Real.sqrt c :=
    (pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 4)).trans
      (le_mul_of_one_le_right (by positivity)
        (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hc1))
  have h1_Sc : 1 ≤ c ^ 4 * Real.sqrt c := h1_c3.trans hc3_Sc
  -- 1. Defect-localized prime cross term
  have hterm_pr : |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
      2 * C_bulk * (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ +
      C_def * (1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N) *
        ‖u‖ * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by
    have h1 := hpr hR' hR6N hlog hu hw
    have h2 : C_bulk * (1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N) ≤
        2 * C_bulk * (c ^ 4 * Real.sqrt c) := by
      have h := mul_le_mul_of_nonneg_left
        (show 1 + (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N ≤
            2 * (c ^ 4 * Real.sqrt c) by
          linarith only [hlog_div25, h1_Sc]) (zero_le_one.trans hC_bulk)
      nlinarith only [h]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
    linarith only [h1, hmul]
  -- 2. Center cross term
  have hterm_cen :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫| ≤
        144 * c ^ 3 * ‖u‖ * ‖w‖ := by
    have h1 := CompletedArithmeticForms.abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
      (completeWeilPoleShift tiltedUnitSpline c) hR' hR6N hlog hu hu1 hw1_orth
    have hpole : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
      rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
      exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
    have h2 : 144 * |completeWeilPoleShift tiltedUnitSpline c| *
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 144 * c ^ 3 := by
      have ha : 144 * |completeWeilPoleShift tiltedUnitSpline c| *
          ((1 + Real.log R') / Real.sqrt (Real.log N)) ≤
          144 * |completeWeilPoleShift tiltedUnitSpline c| * 1 :=
        mul_le_mul_of_nonneg_left hlog_div1 (by positivity)
      have hb : 144 * |completeWeilPoleShift tiltedUnitSpline c| ≤ 144 * c ^ 3 := by
        linarith only [hpole, hc13]
      calc
        144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) =
            144 * |completeWeilPoleShift tiltedUnitSpline c| *
              ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 144 * c ^ 3 := by linarith only [ha, hb]
    exact h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w))
  -- 3. Separated cross error
  have hterm_sep :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫| ≤
        C_sep * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := CompletedArithmeticForms.norm_separatedCrossErrorMatrix_le
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u
    have hcs := (abs_real_inner_le_norm _ w).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg w))
    have h2 : C_sep * c ^ 2 ≤ C_sep * c ^ 3 := mul_le_mul_of_nonneg_left hc23 hC_sep0
    calc
      _ ≤ C_sep * c ^ 2 * ‖u‖ * ‖w‖ := by dsimp only [C_sep]; linarith only [hcs]
      _ ≤ C_sep * c ^ 3 * ‖u‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
  -- 4. Pole error vanishes identically
  have hterm_pole :
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline c N) u, w⟫ = 0 :=
    CompletedArithmeticForms.fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
      tiltedUnitSpline c hN2 hu1 hw1_orth
  -- 5. Overlap minus downward
  have hterm_od :
      |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, w⟫| ≤
        3 * C_od * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := hod hR' hRR_N hlog hc1 hw1 hRNT_lin hu
    have hsqrt_div : Real.sqrt ((1 + Real.log c) / Real.log N) ≤
        2 * c / Real.sqrt (Real.log N) := by
      rw [Real.sqrt_div (by linarith [Real.log_nonneg hc1])]
      exact div_le_div_of_nonneg_right hsqrt_1lc (Real.sqrt_nonneg _)
    have hpart1 : c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) ≤
        2 * c ^ 3 := by
      have h1R0 : 0 ≤ 1 + Real.log R' := by
        have := Real.log_natCast_nonneg R'; linarith only [this]
      calc
        c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) ≤
            c ^ 2 * (1 + Real.log R') * (2 * c / Real.sqrt (Real.log N)) :=
          mul_le_mul_of_nonneg_left hsqrt_div (by positivity)
        _ = 2 * c ^ 3 * ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 2 * c ^ 3 * 1 := mul_le_mul_of_nonneg_left hlog_div1 (by positivity)
        _ = 2 * c ^ 3 := mul_one _
    have hpart2 : c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ c ^ 3 := by
      calc
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) =
            c ^ 2 * ((R' : ℝ) * Real.sqrt (Real.log N / N)) := by ring
        _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hR_sqrt (by positivity)
        _ ≤ c ^ 3 := by linarith only [hc23]
    have hcoef : C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 3 * C_od * c ^ 3 := by
      nlinarith only [hC_od, hpart1, hpart2]
    calc
      _ ≤ ‖Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
            downwardPrimeVector tiltedUnitSpline c N u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (3 * C_od * c ^ 3 * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))) (norm_nonneg w)
      _ = 3 * C_od * c ^ 3 * ‖u‖ * ‖w‖ := by ring
  -- 6. Upward non-ratio vector
  have hterm_up : |⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫| ≤
      2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := hup hR' hlog hc1 hw1 hRNT_up hu
    have hcoef : C_up * c * Real.sqrt (1 + Real.log c) ≤ 2 * C_up * c ^ 3 := by
      calc
        C_up * c * Real.sqrt (1 + Real.log c) ≤ C_up * c * (2 * c) :=
          mul_le_mul_of_nonneg_left hsqrt_1lc (by positivity)
        _ = 2 * C_up * c ^ 2 := by ring
        _ ≤ 2 * C_up * c ^ 3 := mul_le_mul_of_nonneg_left hc23 (by positivity)
    calc
      _ ≤ ‖upwardPrimeVector tiltedUnitSpline c N u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * C_up * c ^ 3 * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))) (norm_nonneg w)
      _ = 2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ := by ring
  have hid_euclid : ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
    intro x; ext n
    change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
    rw [Matrix.one_mulVec]
  have hdecomp :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫ =
        -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ +
        ⟪Matrix.toEuclideanLin
          (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫ -
        ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, w⟫ -
        ⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫ := by
    rw [completeWeilMatrix_eq_decomposition_at_every_overlap contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, hid_euclid,
      CompletedArithmeticForms.fullWeilNonRatioMatrix_eq_downward_add_upward
        contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u,
      inner_add_left, inner_sub_left, real_inner_smul_left, huw_orth, mul_zero, hterm_pole]
    ring
  rw [hdecomp]
  have habs5 : ∀ x₁ x₂ x₃ x₄ x₅ : ℝ,
      |(-x₁) + x₂ - x₃ + x₄ - x₅| ≤ |x₁| + |x₂| + |x₃| + |x₄| + |x₅| := by
    intro x₁ x₂ x₃ x₄ x₅
    have h1 := abs_sub ((-x₁) + x₂ - x₃ + x₄) x₅
    have h2 := abs_add_le ((-x₁) + x₂ - x₃) x₄
    have h3 := abs_sub ((-x₁) + x₂) x₃
    have h4 := abs_add_le (-x₁) x₂
    rw [abs_neg] at h4
    linarith only [h1, h2, h3, h4]
  have hc3_uw : c ^ 3 * ‖u‖ * ‖w‖ ≤ (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc3_Sc (norm_nonneg u)) (norm_nonneg w)
  have hpos_uw : 0 ≤ (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ := by positivity
  have hc_cen : 144 * c ^ 3 * ‖u‖ * ‖w‖ ≤ 144 * (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ := by
    linarith only [hc3_uw]
  have hc_sep : C_sep * c ^ 3 * ‖u‖ * ‖w‖ ≤ C_sep * (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ := by
    have := mul_le_mul_of_nonneg_left hc3_uw hC_sep0; linarith only [this]
  have hc_od : 3 * C_od * c ^ 3 * ‖u‖ * ‖w‖ ≤ 3 * C_od * (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ := by
    have := mul_le_mul_of_nonneg_left hc3_uw (by linarith only [hC_od] : 0 ≤ 3 * C_od)
    linarith only [this]
  have hc_up : 2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ ≤ 2 * C_up * (c ^ 4 * Real.sqrt c) * ‖u‖ * ‖w‖ := by
    have := mul_le_mul_of_nonneg_left hc3_uw (by linarith only [hC_up] : 0 ≤ 2 * C_up)
    linarith only [this]
  have htri := habs5 _ _ _ _ _
  dsimp only [C_cross]
  linarith only [htri, hterm_pr, hterm_cen, hterm_sep, hterm_od, hterm_up,
    hc_cen, hc_sep, hc_od, hc_up, hpos_uw]

/-- **Sharpened high-tail cross-pairing suppression (`m > R'`).**
Absorbs the `poleDefect`-weighted top-strip prime cross-pairing directly into half of the
`(b / c^7) * poleDefect N w` polynomial reserve while retaining the remaining `(b / (2 c^7))`
reserve to make `completeWeilEnergy w` coercive with full `c^9` strength against
`C_cross * (c^4 * √c) * ‖w‖`. -/
private theorem exists_high_tail_suppression_sharpened :
    ∃ C_R C_pdef H_res b_res : ℝ, 0 < C_R ∧ 1 ≤ C_pdef ∧ 0 < H_res ∧ 0 < b_res ∧
      ∀ {Q₁ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → 1 ≤ c → H_res * c ^ 8 ≤ N → c / N ≤ 1 / 3 →
        (∀ {R' : ℕ}, Q₁ ≤ R' → Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁ →
          R' ^ 6 ≤ N ∧
          18 * (1 + Real.log R') ≤ Real.log N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
          (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 ∧
          (1 + Real.log R') ^ 2 * Real.sqrt (1 + Real.log R') / Real.log N ≤
            c ^ 4 * Real.sqrt c ∧
          8 * C_pdef ^ 2 * (c ^ 7 / b_res) *
            (1 / Real.log N + (1 + Real.log R') ^ 4 / (Real.log N) ^ 2) ≤ 1 / 8 ∧
          (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ 1) →
      ∀ {zHat : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        zHat ∈ (conductorSubspace Q₁ N)ᗮ → ‖zHat‖ = 1 →
        completeWeilEnergy tiltedUnitSpline c N zHat ≤
          2 * tiltedSplineSpectralFloorConstant + 2 →
      ∃ R' : ℕ, Q₁ ≤ R' ∧ Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁ ∧
        ∃ u : EuclideanSpace ℝ (PrimeHorizonIndex N),
          u ∈ conductorSubspace R' N ∧ u ∈ (conductorSubspace Q₁ N)ᗮ ∧
          3 / 4 ≤ ‖u‖ ^ 2 ∧ ‖u‖ ≤ 1 ∧
          completeWeilEnergy tiltedUnitSpline c N u ≤
            2 * tiltedSplineSpectralFloorConstant + 3 := by
  obtain ⟨b, B, H, hb, hB, hH, hres⟩ := exists_matrix_polynomial_reserve_local
  obtain ⟨C_cross, C_pdef, hC_cross1, hC_pdef1, hcross⟩ :=
    exists_completeWeilMatrix_orthog_cross_defect_localized
  let M₀ := 2 * tiltedSplineSpectralFloorConstant + 2
  have hM₀ : 0 < M₀ := by
    have := tiltedSplineSpectralFloorConstant_pos; dsimp only [M₀]; positivity
  let K_coef := (B + M₀) / b
  have hK_coef : 0 < K_coef := by dsimp only [K_coef]; positivity
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let C_gap := D * (1 + 2 * (B + 8 * C_cross ^ 2) / b)
  have hC_gap : 0 < C_gap := by dsimp only [C_gap]; positivity
  let C_app := 16 * quadraticConfinementConstant * (K_coef + 1)
  have hC_app : 0 < C_app := by
    have := quadraticConfinementConstant_pos; dsimp only [C_app]; positivity
  let C_R := C_app + C_gap + 1
  have hC_R : 0 < C_R := by dsimp only [C_R]; positivity
  refine ⟨C_R, C_pdef, H, b, hC_R, hC_pdef1, hH, hb, ?_⟩
  intro Q₁ N c hQ₁ hc1 hHN hw1 hR'_conds zHat hz_orth hz_norm hz_energy
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc16 : 1 ≤ c ^ 16 := one_le_pow₀ hc1
  have hdef_le : poleDefect N (primeHorizonExtension zHat) ≤ K_coef * c ^ 16 := by
    have hr := hres c hc1 N hHN zHat
    rw [hz_norm, one_pow, mul_one] at hr
    have h1 : (b / c ^ 7) * poleDefect N (primeHorizonExtension zHat) ≤
        B * c ^ 9 + M₀ := by dsimp only [M₀]; linarith only [hr, hz_energy]
    have hc9 : 1 ≤ c ^ 9 := one_le_pow₀ hc1
    have h2 : B * c ^ 9 + M₀ ≤ (B + M₀) * c ^ 9 := by nlinarith only [hM₀, hc9]
    have h3 := (div_le_iff₀ (pow_pos hc0 7)).mp (by
      simpa only [div_mul_eq_mul_div] using h1.trans h2)
    dsimp only [K_coef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    calc
      poleDefect N (primeHorizonExtension zHat) * b =
          b * poleDefect N (primeHorizonExtension zHat) := mul_comm _ _
      _ ≤ (B + M₀) * c ^ 9 * c ^ 7 := h3
      _ = (B + M₀) * c ^ 16 := by ring
  obtain ⟨R₀, _, hR₀log, happ⟩ := exists_explicit_quadratic_conductor_projection
    (1 / 4) (by norm_num) (by norm_num) (K_coef * c ^ 16) (by positivity)
  have hR₀bound : Real.log R₀ ≤ C_app * c ^ 16 := by
    have hK1 : K_coef * c ^ 16 + 1 ≤ (K_coef + 1) * c ^ 16 := by linarith only [hc16]
    calc
      _ ≤ quadraticConfinementConstant / (1 / 4 : ℝ) ^ 2 * (K_coef * c ^ 16 + 1) := hR₀log
      _ ≤ quadraticConfinementConstant / (1 / 4 : ℝ) ^ 2 * ((K_coef + 1) * c ^ 16) :=
        mul_le_mul_of_nonneg_left hK1 (by have := quadraticConfinementConstant_pos; positivity)
      _ = _ := by dsimp only [C_app]; ring
  let G : ℕ := ⌈Real.exp (C_gap * c ^ 16)⌉₊
  have hXpos : 0 < C_gap * c ^ 16 := mul_pos hC_gap (pow_pos hc0 16)
  have hexp1 : 1 < Real.exp (C_gap * c ^ 16) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hXpos
  have hceil : Real.exp (C_gap * c ^ 16) ≤ (G : ℝ) := Nat.le_ceil _
  have hGpos : (0 : ℝ) < G := (zero_lt_one.trans hexp1).trans_le hceil
  have hGlow : C_gap * c ^ 16 ≤ Real.log G := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hceil
  have hGup : Real.log G ≤ C_gap * c ^ 16 + 1 := by
    have hceilUp : (G : ℝ) < Real.exp (C_gap * c ^ 16) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hdouble : (G : ℝ) ≤ 2 * Real.exp (C_gap * c ^ 16) := by
      linarith only [hceilUp, hexp1]
    have hlog := Real.log_le_log hGpos hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
    linarith only [hlog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let R := max R₀ G
  let R' := max R Q₁
  have hQR' : Q₁ ≤ R' := le_max_right _ _
  have hR₀R' : R₀ ≤ R' := (le_max_left R₀ G).trans (le_max_left R Q₁)
  have hGR' : G ≤ R' := (le_max_right R₀ G).trans (le_max_left R Q₁)
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRbound : Real.log R ≤ C_R * c ^ 16 := by
    rcases le_total R₀ G with hRG | hGR
    · rw [show R = G from max_eq_right hRG]
      dsimp only [C_R]
      nlinarith only [hGup, hc16, hC_app, pow_nonneg hc0.le 16]
    · rw [show R = R₀ from max_eq_left hGR]
      dsimp only [C_R]
      nlinarith only [hR₀bound, hC_gap, pow_nonneg hc0.le 16]
  have hR'_log : Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁ := by
    have hQlog := Real.log_natCast_nonneg Q₁
    have hCr : 0 ≤ C_R * c ^ 16 := by positivity
    rcases le_total R Q₁ with hRQ | hQR
    · rw [show R' = Q₁ from max_eq_right hRQ]; linarith only [hCr]
    · rw [show R' = R from max_eq_left hQR]; linarith only [hRbound, hQlog]
  have hgapLog : C_gap * c ^ 16 ≤ Real.log R' :=
    hGlow.trans (Real.log_le_log hGpos (by exact_mod_cast hGR'))
  obtain ⟨hR6N, hlogN, hRNT_lin, hRNT_up, hlog_div1, hlog_div25, hpdef_small, hR_sqrt⟩ :=
    hR'_conds hQR' hR'_log
  have hN2 : 2 ≤ N := by
    have hpow : R' ^ 1 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simp only [pow_one] at hpow
    omega
  have hL0 : 0 < Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlogN, this]
  let u := (conductorSubspace R' N).starProjection zHat
  let w := zHat - u
  have hu_mem : u ∈ conductorSubspace R' N :=
    (conductorSubspace R' N).starProjection_apply_mem zHat
  have hu_orthQ : u ∈ (conductorSubspace Q₁ N)ᗮ :=
    starProjection_mem_orthogonal_of_le (conductorSubspace_mono hQR' N) hz_orth
  have hu_orth1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu_orthQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have hw_orth : w ∈ (conductorSubspace R' N)ᗮ := by
    rw [Submodule.mem_orthogonal]; intro v hv; rw [real_inner_comm]
    exact (conductorSubspace R' N).starProjection_inner_eq_zero zHat v hv
  have hw_sq : ‖w‖ ^ 2 ≤ 1 / 4 := by
    have hpR_mem : (conductorSubspace R₀ N).starProjection zHat ∈ conductorSubspace R' N :=
      conductorSubspace_mono hR₀R' N ((conductorSubspace R₀ N).starProjection_apply_mem zHat)
    exact (norm_sub_starProjection_sq_le (conductorSubspace R' N) zHat _ hpR_mem).trans
      (happ N hN2 zHat hz_norm.le hdef_le)
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace R' N) zHat
  change ‖u‖ ^ 2 + ‖w‖ ^ 2 = ‖zHat‖ ^ 2 at hpyth
  rw [hz_norm, one_pow] at hpyth
  have hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2 := by linarith only [hpyth, hw_sq]
  have hu_le1 : ‖u‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖w‖, norm_nonneg u]
  have hw_def : (Real.log R' / D - 1) * ‖w‖ ^ 2 ≤ poleDefect N (primeHorizonExtension w) := by
    by_cases hw0 : ‖w‖ = 0
    · rw [hw0, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact poleDefect_nonneg _ _
    have hp0 : (conductorSubspace R' N).starProjection w = 0 := by
      let p := (conductorSubspace R' N).starProjection w
      have hp_mem : p ∈ conductorSubspace R' N :=
        (conductorSubspace R' N).starProjection_apply_mem w
      have hi : ⟪p, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hp_mem hw_orth
      have hi' : ⟪w, p⟫ = 0 := by simpa only [real_inner_comm] using hi
      have hj := (conductorSubspace R' N).starProjection_inner_eq_zero w p hp_mem
      rw [inner_sub_left] at hj
      change ⟪w, p⟫ - ⟪p, p⟫ = 0 at hj
      rw [hi', real_inner_self_eq_norm_sq] at hj
      apply norm_eq_zero.mp
      nlinarith only [hj, norm_nonneg p]
    apply poleDefect_ge_explicit_of_norm_sub_starProjection_gt hR'2 hN2
    rw [hp0, sub_zero]
    exact by linarith only [sq_pos_of_ne_zero hw0]
  -- Split `(b / c^7) * poleDefect` into half for `‖w‖^2` coercivity and half for top-strip `√poleDefect`.
  have hgapCoeff : 2 * (B + 8 * C_cross ^ 2) * c ^ 16 ≤ b * (Real.log R' / D - 1) := by
    have hlow : (1 + 2 * (B + 8 * C_cross ^ 2) / b) * c ^ 16 ≤ Real.log R' / D := by
      apply (le_div_iff₀ hD).mpr
      calc
        ((1 + 2 * (B + 8 * C_cross ^ 2) / b) * c ^ 16) * D = C_gap * c ^ 16 := by
          dsimp only [C_gap]; ring
        _ ≤ Real.log R' := hgapLog
    have hs := mul_le_mul_of_nonneg_left hlow hb.le
    have he : b * ((1 + 2 * (B + 8 * C_cross ^ 2) / b) * c ^ 16) =
        b * c ^ 16 + 2 * (B + 8 * C_cross ^ 2) * c ^ 16 := by
      field_simp [hb.ne']
    rw [he] at hs
    nlinarith only [hs, mul_le_mul_of_nonneg_left hc16 hb.le]
  have hgap9 : (B + 8 * C_cross ^ 2) * c ^ 9 ≤
      (b / (2 * c ^ 7)) * (Real.log R' / D - 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 2 * c ^ 7)]
    calc
      (B + 8 * C_cross ^ 2) * c ^ 9 * (2 * c ^ 7) =
          2 * (B + 8 * C_cross ^ 2) * c ^ 16 := by ring
      _ ≤ b * (Real.log R' / D - 1) := hgapCoeff
  have hw_energy :
      (b / (2 * c ^ 7)) * poleDefect N (primeHorizonExtension w) +
        8 * C_cross ^ 2 * c ^ 9 * ‖w‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N w := by
    have hr := hres c hc1 N hHN w
    have hsplit_b : (b / c ^ 7) * poleDefect N (primeHorizonExtension w) =
        (b / (2 * c ^ 7)) * poleDefect N (primeHorizonExtension w) +
          (b / (2 * c ^ 7)) * poleDefect N (primeHorizonExtension w) := by ring
    have hd := mul_le_mul_of_nonneg_left hw_def
      (div_nonneg hb.le (by positivity : 0 ≤ 2 * c ^ 7))
    have hg := mul_le_mul_of_nonneg_right hgap9 (sq_nonneg ‖w‖)
    nlinarith only [hr, hsplit_b, hd, hg]
  have htail_cost :
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| -
        completeWeilEnergy tiltedUnitSpline c N w ≤ 1 / 4 := by
    have hcross' := hcross hR'2 hR6N hlogN hc1 hw1 hRNT_lin hRNT_up hlog_div1 hlog_div25
      hR_sqrt hu_mem hu_orth1 hw_orth
    let S_top := 1 / Real.sqrt (Real.log N) + (1 + Real.log R') ^ 2 / Real.log N
    have hStop0 : 0 ≤ S_top := by dsimp only [S_top]; positivity
    have hStop_sq : S_top ^ 2 ≤
        2 * (1 / Real.log N + (1 + Real.log R') ^ 4 / (Real.log N) ^ 2) := by
      dsimp only [S_top]
      have h1 : (1 / Real.sqrt (Real.log N)) ^ 2 = 1 / Real.log N := by
        rw [div_pow, one_pow, Real.sq_sqrt hL0.le]
      have h2 : ((1 + Real.log R') ^ 2 / Real.log N) ^ 2 =
          (1 + Real.log R') ^ 4 / (Real.log N) ^ 2 := by rw [div_pow]; ring
      nlinarith only [h1, h2,
        sq_nonneg (1 / Real.sqrt (Real.log N) - (1 + Real.log R') ^ 2 / Real.log N)]
    have hcross_bound :
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
          2 * C_cross * (c ^ 4 * Real.sqrt c) * ‖w‖ +
          2 * C_pdef * S_top * Real.sqrt (poleDefect N (primeHorizonExtension w)) := by
      have hh1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu_le1
          (show 0 ≤ C_cross * (c ^ 4 * Real.sqrt c) by positivity))
        (norm_nonneg w)
      have hh2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu_le1
          (mul_nonneg (zero_le_one.trans hC_pdef1) hStop0))
        (Real.sqrt_nonneg (poleDefect N (primeHorizonExtension w)))
      dsimp only [S_top] at hh2 ⊢
      nlinarith only [hcross', hh1, hh2]
    have hyoung_w :
        2 * C_cross * (c ^ 4 * Real.sqrt c) * ‖w‖ -
          8 * C_cross ^ 2 * c ^ 9 * ‖w‖ ^ 2 ≤ 1 / 8 := by
      have hSc_sq : (c ^ 4 * Real.sqrt c) ^ 2 = c ^ 9 := by
        rw [mul_pow, Real.sq_sqrt hc0.le]; ring
      have hsq : 0 ≤ (4 * C_cross * (c ^ 4 * Real.sqrt c) * ‖w‖ - 1 / 4) ^ 2 := sq_nonneg _
      have hexp : (4 * C_cross * (c ^ 4 * Real.sqrt c) * ‖w‖ - 1 / 4) ^ 2 =
          16 * C_cross ^ 2 * (c ^ 4 * Real.sqrt c) ^ 2 * ‖w‖ ^ 2 -
            2 * C_cross * (c ^ 4 * Real.sqrt c) * ‖w‖ + 1 / 16 := by ring
      rw [hSc_sq] at hexp
      have hnonneg : 0 ≤ C_cross ^ 2 * c ^ 9 * ‖w‖ ^ 2 := by positivity
      linarith only [hsq, hexp, hnonneg]
    have hyoung_def :
        2 * C_pdef * S_top * Real.sqrt (poleDefect N (primeHorizonExtension w)) -
          (b / (2 * c ^ 7)) * poleDefect N (primeHorizonExtension w) ≤ 1 / 8 := by
      let sr_b := Real.sqrt (b / (2 * c ^ 7))
      let sr_d := Real.sqrt (poleDefect N (primeHorizonExtension w))
      have hsrb_pos : 0 < sr_b := Real.sqrt_pos.mpr (by positivity)
      have hsrb_sq : sr_b ^ 2 = b / (2 * c ^ 7) := Real.sq_sqrt (by positivity)
      have hsrd_sq : sr_d ^ 2 = poleDefect N (primeHorizonExtension w) :=
        Real.sq_sqrt (poleDefect_nonneg _ _)
      have hsq_term : (C_pdef * S_top / sr_b) ^ 2 ≤ 1 / 8 := by
        rw [div_pow, mul_pow, hsrb_sq]
        have heq : C_pdef ^ 2 * S_top ^ 2 / (b / (2 * c ^ 7)) =
            2 * C_pdef ^ 2 * (c ^ 7 / b) * S_top ^ 2 := by
          field_simp [hb.ne', hc0.ne']; ring
        rw [heq]
        calc
          2 * C_pdef ^ 2 * (c ^ 7 / b) * S_top ^ 2 ≤
              2 * C_pdef ^ 2 * (c ^ 7 / b) *
                (2 * (1 / Real.log N + (1 + Real.log R') ^ 4 / (Real.log N) ^ 2)) :=
            mul_le_mul_of_nonneg_left hStop_sq (by positivity)
          _ = 4 * C_pdef ^ 2 * (c ^ 7 / b) *
                (1 / Real.log N + (1 + Real.log R') ^ 4 / (Real.log N) ^ 2) := by ring
          _ ≤ 8 * C_pdef ^ 2 * (c ^ 7 / b) *
                (1 / Real.log N + (1 + Real.log R') ^ 4 / (Real.log N) ^ 2) := by
            have : 0 ≤ C_pdef ^ 2 * (c ^ 7 / b) *
                (1 / Real.log N + (1 + Real.log R') ^ 4 / (Real.log N) ^ 2) := by positivity
            linarith only [this]
          _ ≤ 1 / 8 := hpdef_small
      have hprod : 2 * C_pdef * S_top * sr_d = 2 * (C_pdef * S_top / sr_b) * (sr_b * sr_d) := by
        field_simp [hsrb_pos.ne']
      have hdiff_sq : 0 ≤ (sr_b * sr_d - C_pdef * S_top / sr_b) ^ 2 := sq_nonneg _
      have hexp_sq : (sr_b * sr_d - C_pdef * S_top / sr_b) ^ 2 =
          (b / (2 * c ^ 7)) * poleDefect N (primeHorizonExtension w) -
            2 * (C_pdef * S_top / sr_b) * (sr_b * sr_d) + (C_pdef * S_top / sr_b) ^ 2 := by
        calc
          (sr_b * sr_d - C_pdef * S_top / sr_b) ^ 2 =
              sr_b ^ 2 * sr_d ^ 2 - 2 * (C_pdef * S_top / sr_b) * (sr_b * sr_d) +
                (C_pdef * S_top / sr_b) ^ 2 := by ring
          _ = _ := by rw [hsrb_sq, hsrd_sq]
      dsimp only [sr_d] at hprod hexp_sq
      linarith only [hprod, hdiff_sq, hexp_sq, hsq_term]
    linarith only [hcross_bound, hw_energy, hyoung_w, hyoung_def]
  have hu_energy : completeWeilEnergy tiltedUnitSpline c N u ≤
      2 * tiltedSplineSpectralFloorConstant + 3 := by
    have hz_split : zHat = u + w := by dsimp only [w]; abel
    have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N)) w u
    have hexp : completeWeilEnergy tiltedUnitSpline c N (u + w) =
        completeWeilEnergy tiltedUnitSpline c N u +
          2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫ +
          completeWeilEnergy tiltedUnitSpline c N w := by
      unfold completeWeilEnergy
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
        real_inner_comm w (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u)]
      ring
    rw [← hz_split] at hexp
    linarith only [hexp, hz_energy, htail_cost,
      neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫]
  exact ⟨R', hQR', hR'_log, u, hu_mem, hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩

private theorem hermitian_inner_add_eq_local {N : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin A (x + y), x + y⟫ =
      ⟪Matrix.toEuclideanLin A x, x⟫ + 2 * ⟪Matrix.toEuclideanLin A x, y⟫ +
        ⟪Matrix.toEuclideanLin A y, y⟫ := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) y x
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
    real_inner_comm y (Matrix.toEuclideanLin A x)]
  ring

private theorem completeWeilEnergy_add_eq_local (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) =
      completeWeilEnergy φ c N x +
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y :=
  hermitian_inner_add_eq_local (completeWeilMatrix_isHermitian φ c N) x y

private theorem renormalizedPrimeEnergy_add_eq_local {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    renormalizedPrimeEnergy N (x + y) =
      renormalizedPrimeEnergy N x + renormalizedPrimeEnergy N y +
        2 * ⟪Real.log N • x - Matrix.toEuclideanLin (fullPrimeMatrix N) x, y⟫ := by
  have hnorm : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm y x, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  unfold renormalizedPrimeEnergy
  rw [hnorm, hermitian_inner_add_eq_local (fullPrimeMatrix_isHermitian N) x y,
    inner_sub_left, real_inner_smul_left]
  ring

private theorem sub_starProjection_mem_orthogonal_local {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    x - K.starProjection x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [real_inner_comm]
  exact K.starProjection_inner_eq_zero x v hv

private theorem exists_raw_approx_of_starProjection_sq_le_local {Q N : ℕ} (hN : 2 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (h : ‖x - (conductorSubspace Q N).starProjection x‖ ^ 2 ≤ 1 / 4) :
    ∃ b : ℕ → ℝ,
      (∑ n ∈ Icc 1 N,
        (primeHorizonExtension x n -
          ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4 := by
  let p := (conductorSubspace Q N).starProjection x
  obtain ⟨a, -, hp_eq⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := p)).mp
    ((conductorSubspace Q N).starProjection_apply_mem x)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog
  let b : ℕ → ℝ := fun m => a m / Real.sqrt (Real.log N)
  refine ⟨b, ?_⟩
  have hsum_eq : (∑ n ∈ Icc 1 N,
      (primeHorizonExtension x n -
        ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n) ^ 2) = ‖x - p‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq (x - p)]
    refine sum_congr rfl fun n hn => ?_
    congr 1
    rw [primeHorizonExtension_coe (x - p) ⟨n, hn⟩, primeHorizonExtension_coe x ⟨n, hn⟩]
    change x ⟨n, hn⟩ - ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n = x ⟨n, hn⟩ - p ⟨n, hn⟩
    congr 1
    rw [hp_eq]
    change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
      (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    change b m * ramanujanPoleProfile m n =
      a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n)
    dsimp only [b]
    field_simp [hs.ne']
  rw [hsum_eq]
  exact h

private theorem low_band_decoupling_unit_orthogonal_local {Q₁ N : ℕ} {c : ℝ}
    (hQ₁ : 2 ≤ Q₁) (hQN : Q₁ * Q₁ ≤ N)
    (hlog : 18 * (1 + Real.log Q₁) ≤ Real.log N) (hc1 : 1 ≤ c)
    (hres_sum : (∑ m ∈ Icc 1 Q₁,
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m •
          normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 1 / 128)
    (hgram_err : 9 * (1 + Real.log Q₁) / Real.log N *
      (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4) ≤ 1 / 16)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : ‖x‖ = 1)
    (hxE : completeWeilEnergy tiltedUnitSpline c N x ≤ tiltedSplineSpectralFloorConstant / 2)
    (hdist : 1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2) :
    ∃ zHat : EuclideanSpace ℝ (PrimeHorizonIndex N),
      zHat ∈ (conductorSubspace Q₁ N)ᗮ ∧ ‖zHat‖ = 1 ∧
      completeWeilEnergy tiltedUnitSpline c N zHat ≤
        2 * tiltedSplineSpectralFloorConstant + 2 := by
  let p := (conductorSubspace Q₁ N).starProjection x
  let z := x - p
  have hz_orth : z ∈ (conductorSubspace Q₁ N)ᗮ := sub_starProjection_mem_orthogonal_local _ x
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace Q₁ N) x
  change ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 at hpyth
  rw [hx, one_pow] at hpyth
  have hp_le1 : ‖p‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖z‖, norm_nonneg p]
  have hz_le1 : ‖z‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖p‖, norm_nonneg z]
  have hz_gt : 1 / 2 < ‖z‖ := by nlinarith only [hdist, norm_nonneg z]
  have hz_pos : 0 < ‖z‖ := by linarith only [hz_gt]
  obtain ⟨a, -, hp_eq⟩ := (mem_conductorSubspace_iff (M := Q₁) (N := N) (x := p)).mp
    ((conductorSubspace Q₁ N).starProjection_apply_mem x)
  have ha_sq : (∑ m ∈ Icc 1 Q₁, a m ^ 2) ≤ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hQ₁ hQN hlog a).1
    rw [← hp_eq] at hr
    nlinarith only [hr, hpyth, sq_nonneg ‖z‖]
  let r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun m =>
    Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N
  let dVec := ∑ m ∈ Icc 1 Q₁,
    (a m * completedConductorEnergy tiltedUnitSpline c m) •
      normalizedRamanujanHorizonVector m N
  let rVec := ∑ m ∈ Icc 1 Q₁, a m • r m
  have hWp_eq : Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) p =
      dVec + rVec := by
    rw [hp_eq, map_sum]
    dsimp only [dVec, rVec, r]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_sub, mul_smul]
    abel
  have hrVec_norm : ‖rVec‖ ≤ 1 / 8 := by
    have htri : ‖rVec‖ ≤ ∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 Q₁) (fun m => |a m|) (fun m => ‖r m‖)
    simp only [sq_abs] at hcs
    have hsq : (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
      calc
        _ ≤ (∑ m ∈ Icc 1 Q₁, a m ^ 2) * ∑ m ∈ Icc 1 Q₁, ‖r m‖ ^ 2 := hcs
        _ ≤ 2 * (1 / 128) := mul_le_mul ha_sq hres_sum
          (sum_nonneg fun _ _ => sq_nonneg _) zero_le_two
        _ = (1 / 8 : ℝ) ^ 2 := by norm_num
    have hsum0 : 0 ≤ ∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖ :=
      sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hle : (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) ≤ 1 / 8 := by nlinarith only [hsq, hsum0]
    exact htri.trans hle
  have hcross : |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) p, z⟫| ≤
      1 / 8 := by
    have hd_mem : dVec ∈ conductorSubspace Q₁ N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N _
    have hd_orth : ⟪dVec, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hd_mem hz_orth
    rw [hWp_eq, inner_add_left, hd_orth, zero_add]
    exact (abs_real_inner_le_norm rVec z).trans
      ((mul_le_mul hrVec_norm hz_le1 (norm_nonneg z) (by norm_num)).trans_eq (mul_one _))
  have hd_self : -(1 / 8 : ℝ) ≤ ⟪dVec, p⟫ := by
    let M_E := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4
    have hE_bounds : ∀ m ∈ Icc 1 Q₁,
        0 ≤ completedConductorEnergy tiltedUnitSpline c m ∧
          completedConductorEnergy tiltedUnitSpline c m ≤ M_E := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hpos : 0 ≤ completedConductorEnergy tiltedUnitSpline c m := by
        have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc1 hm1
        have hpos' : 0 < (2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2) / c ^ 7 :=
          div_pos tiltedSplineSpectralFloorConstant_pos (pow_pos (zero_lt_one.trans_le hc1) 7)
        linarith only [hf, hpos']
      have hlogm : Real.log m ≤ Real.log Q₁ :=
        Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmQ)
      have hup := completedConductorEnergy_le_of_one_le contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc1 hm1
      exact ⟨hpos, by dsimp only [M_E]; linarith only [hup, hlogm]⟩
    have hME0 : 0 ≤ M_E := by
      have h2mem : 2 ∈ Icc 1 Q₁ := mem_Icc.mpr ⟨by omega, hQ₁⟩
      exact (hE_bounds 2 h2mem).1.trans (hE_bounds 2 h2mem).2
    have hdiag_nonneg : 0 ≤ ∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy tiltedUnitSpline c m) * a m :=
      sum_nonneg fun m hm => by
        have h := (hE_bounds m hm).1
        nlinarith only [h, sq_nonneg (a m)]
    have hd_sq_le : (∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy tiltedUnitSpline c m) ^ 2) ≤
        M_E ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      obtain ⟨h0, hup⟩ := hE_bounds m hm
      have hesq : completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤ M_E ^ 2 :=
        pow_le_pow_left₀ h0 hup 2
      nlinarith only [hesq, sq_nonneg (a m)]
    have hsqrt_d :
        Real.sqrt (∑ m ∈ Icc 1 Q₁,
          (a m * completedConductorEnergy tiltedUnitSpline c m) ^ 2) ≤
          M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := by
      calc
        _ ≤ Real.sqrt (M_E ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2) := Real.sqrt_le_sqrt hd_sq_le
        _ = M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hME0]
    have hpol := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hQ₁ hQN
      (fun m => a m * completedConductorEnergy tiltedUnitSpline c m) a
    rw [← hp_eq] at hpol
    have hcoef0 : 0 ≤ 9 * (1 + Real.log Q₁) / Real.log N := by
      have hL : 0 < Real.log N := by
        have := Real.log_natCast_nonneg Q₁; linarith only [hlog, this]
      have := Real.log_natCast_nonneg Q₁; positivity
    have herr_le : |⟪dVec, p⟫ - ∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy tiltedUnitSpline c m) * a m| ≤ 1 / 8 := by
      calc
        _ ≤ 9 * (1 + Real.log Q₁) / Real.log N *
              Real.sqrt (∑ m ∈ Icc 1 Q₁,
                (a m * completedConductorEnergy tiltedUnitSpline c m) ^ 2) *
              Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := hpol
        _ ≤ 9 * (1 + Real.log Q₁) / Real.log N *
              (M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2)) *
              Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrt_d hcoef0) (Real.sqrt_nonneg _)
        _ = (9 * (1 + Real.log Q₁) / Real.log N * M_E) * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
          rw [mul_assoc, mul_assoc, Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
          ring
        _ ≤ (1 / 16) * 2 := mul_le_mul hgram_err ha_sq
          (sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    linarith only [(abs_le.mp herr_le).1, hdiag_nonneg]
  have hp_self : -(1 / 4 : ℝ) ≤ completeWeilEnergy tiltedUnitSpline c N p := by
    unfold completeWeilEnergy
    rw [hWp_eq, inner_add_left]
    have hr_p : |⟪rVec, p⟫| ≤ 1 / 8 :=
      (abs_real_inner_le_norm rVec p).trans
        ((mul_le_mul hrVec_norm hp_le1 (norm_nonneg p) (by norm_num)).trans_eq (mul_one _))
    linarith only [hd_self, (abs_le.mp hr_p).1]
  have hz_energy : completeWeilEnergy tiltedUnitSpline c N z ≤
      tiltedSplineSpectralFloorConstant / 2 + 1 / 2 := by
    have hx_split : x = p + z := by dsimp only [z]; abel
    have hexp := completeWeilEnergy_add_eq_local tiltedUnitSpline c p z
    rw [← hx_split] at hexp
    linarith only [hexp, hxE, hp_self, (abs_le.mp hcross).1]
  let zHat := (‖z‖)⁻¹ • z
  refine ⟨zHat, Submodule.smul_mem _ _ hz_orth, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz_pos, inv_mul_cancel₀ hz_pos.ne']
  · have hscale : completeWeilEnergy tiltedUnitSpline c N zHat =
        (‖z‖⁻¹) ^ 2 * completeWeilEnergy tiltedUnitSpline c N z := by
      dsimp only [zHat, completeWeilEnergy]
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hscale]
    have hkappa0 : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
    rcases le_or_gt (completeWeilEnergy tiltedUnitSpline c N z) 0 with hneg | hpos
    · have hle0 : (‖z‖⁻¹) ^ 2 * completeWeilEnergy tiltedUnitSpline c N z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg
      linarith only [hle0, hkappa0]
    · have hinv_lt : (‖z‖⁻¹) ^ 2 ≤ 4 := by
        have h1 : ‖z‖⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀' hz_pos).mpr (by linarith only [hz_gt])
        calc
          (‖z‖⁻¹) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
          _ = 4 := by norm_num
      calc
        (‖z‖⁻¹) ^ 2 * completeWeilEnergy tiltedUnitSpline c N z ≤
            4 * (tiltedSplineSpectralFloorConstant / 2 + 1 / 2) :=
          mul_le_mul hinv_lt hz_energy hpos.le (by norm_num)
        _ = 2 * tiltedSplineSpectralFloorConstant + 2 := by ring

/-- Integer-separation support vanishing of both `overlapMatrix φ c N x` and
`downwardPrimeVector φ c N x` at every coordinate `idx` with `linearNearRowRadius c + 1 ≤ N / idx`. -/
private theorem overlap_sub_downward_apply_eq_zero_of_quotient_ge {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hN1 : 1 ≤ N) (hw1 : c / N ≤ 1 / 3)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (idx : PrimeHorizonIndex N)
    (hquot : linearNearRowRadius c + 1 ≤ (N : ℝ) / (idx.1 : ℝ)) :
    (Matrix.toEuclideanLin (overlapMatrix φ c N) x) idx = 0 ∧
      downwardPrimeVector φ c N x idx = 0 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hn1 : 1 ≤ idx.1 := (mem_Icc.mp idx.2).1
  have hn1R : (1 : ℝ) ≤ idx.1 := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < idx.1 := zero_lt_one.trans_le hn1R
  have hN_gt : linearNearRowRadius c * (idx.1 : ℝ) < (N : ℝ) := by
    have hle := (le_div_iff₀ hn0).mp hquot
    nlinarith only [hle, hn1R]
  constructor
  · change ((overlapMatrix φ c N) *ᵥ x.ofLp) idx = 0
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hov0 : overlapMatrix φ c N idx j = 0 := by
      unfold overlapMatrix
      rw [if_neg]
      rintro ⟨hne, hlog⟩
      have hj_near : j.1 ∈ nearRowIndices c N idx.1 :=
        mem_filter.mpr ⟨j.2, Ne.symm hne, by rw [mul_div_assoc]; exact hlog⟩
      have hge := (nearRow_geometry_small_width hc0 idx.2 hj_near hw).2.1
      linarith only [hge, hN_gt]
    rw [hov0, zero_mul]
  · obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw0
    change downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) idx.1 /
        (∫ u, atomDilate φ (c / N) u ^ 2) = 0
    rw [downwardPrimeRow_eq_sum hgsupp hw0.le idx.2 (primeHorizonExtension x), div_eq_zero_iff]
    left
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
    · suffices hsum0 : (∑ j ∈ Icc 1 N, primeHorizonExtension x j *
          (if idx.1 = k * j then 0
           else bumpCorr (atomDilate φ (c / N))
             (Real.log k - (Real.log idx.1 - Real.log j)))) = 0 by
        rw [hsum0, mul_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      by_cases hkj : idx.1 = k * j
      · rw [if_pos hkj, mul_zero]
      · rw [if_neg hkj]
        have hb0 : bumpCorr (atomDilate φ (c / N))
            (Real.log k - (Real.log idx.1 - Real.log j)) = 0 := by
          apply bumpCorr_eq_zero hgsupp
          by_contra hnot
          have hle : |Real.log k - (Real.log idx.1 - Real.log j)| ≤ c / N :=
            le_of_not_gt hnot
          have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
          have hkj1 : 1 ≤ k * j := Nat.mul_pos (by omega) (by omega)
          have hk0R : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
          have hj0R : (0 : ℝ) < j := by exact_mod_cast hj1
          have hlog_eq : |Real.log (idx.1 : ℝ) - Real.log ((k * j : ℕ) : ℝ)| =
              |Real.log k - (Real.log idx.1 - Real.log j)| := by
            rw [← abs_neg]
            congr 1
            push_cast
            rw [Real.log_mul hk0R.ne' hj0R.ne']
            ring
          have hsep := (logWindow_integer_separation_small_width hc0 hN1 hkj1 hn1
            (Ne.symm hkj) (hlog_eq.trans_le hle) hw).2
          have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
          have hrad_ge : c * Real.exp 1 ≤ linearNearRowRadius c := by
            unfold linearNearRowRadius
            nlinarith only [hc0, he12, Real.exp_pos 1]
          have hge : (N : ℝ) ≤ linearNearRowRadius c * (idx.1 : ℝ) :=
            hsep.trans (mul_le_mul_of_nonneg_right hrad_ge hn0.le)
          linarith only [hge, hN_gt]
        rw [hb0, mul_zero]

/-- **Sharpened complete-Weil quadratic reduction on `conductorSubspace R' N ⊓ (conductorSubspace 1 N)ᗮ`.**
Pairing `overlapMatrix u - downwardPrimeVector u` against the quotient-tail restriction of `u` on
`{n ∈ Icc 1 N | N / n < linearNearRowRadius c + 1}` gains an extra factor of `√((1 + log c) / log N)`,
replacing `c^2 * (1 + log R') * √((1 + log c) / log N)` by `c^2 * (1 + log c) * (1 + log R') / log N`. -/
private theorem exists_completeWeilEnergy_ge_prime_sub_overlap_sharpened :
    ∃ C_dec C_err : ℝ, 0 < C_dec ∧ 0 < C_err ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_err * (c * (1 + Real.log R') / Real.sqrt (Real.log N) +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ → ‖u‖ ≤ 1 →
        renormalizedPrimeEnergy N u -
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ -
            Real.log c - C_dec ≤
          completeWeilEnergy tiltedUnitSpline c N u := by
  obtain ⟨C_od, hC_od, hod⟩ :=
    CompletedArithmeticForms.exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep' := 36 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep'0 : 0 ≤ C_sep' := by
    have := integral_tiltedUnitSpline_sq_pos; dsimp only [C_sep']; positivity
  let C_err := 144 + C_sep' + 20 * C_od + 1
  let C_dec := |completeWeilSelfFinitePart tiltedUnitSpline 1| +
    |Real.eulerMascheroniConstant| + 3
  refine ⟨C_dec, C_err, by dsimp only [C_dec]; positivity,
    by dsimp only [C_err]; positivity, ?_⟩
  intro R' N c hR' hR6N hlog hc1 hw1 hRNT herr u hu hu1 hu_le1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hR4_N : R' ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 6)).trans hR6N
  have hN2 : 2 ≤ N := by have := Nat.mul_le_mul hR' hR'; omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hcN : c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hu_sq_le1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith only [hu_le1, norm_nonneg u]
  have hself_eq : completeWeilSelfFinitePart tiltedUnitSpline c =
      completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.log c := by
    unfold completeWeilSelfFinitePart
    rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc0.ne',
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  have hself_err : |completeWeilSelfError tiltedUnitSpline c N| ≤ 1 := by
    have h1 := abs_completeWeilSelfError_le_of_width_le_one contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 hcN
    have he12 : Real.exp (1 / 2) ≤ 3 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans he1
    calc
      |completeWeilSelfError tiltedUnitSpline c N| ≤
          Real.exp (1 / 2) / 2 * (c / N) := h1
      _ ≤ (3 / 2) * (1 / 3) :=
        mul_le_mul (by linarith only [he12]) hw1 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hself_term :
      -Real.log c - (|completeWeilSelfFinitePart tiltedUnitSpline 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
        completeWeilSelfError tiltedUnitSpline c N) * ‖u‖ ^ 2 := by
    rw [hself_eq]
    have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hlc_u : Real.log c * ‖u‖ ^ 2 ≤ Real.log c :=
      (mul_le_mul_of_nonneg_left hu_sq_le1 hlc0).trans_eq (mul_one _)
    have hconst_lb : -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant +
        completeWeilSelfError tiltedUnitSpline c N) := by
      linarith only [neg_abs_le (completeWeilSelfFinitePart tiltedUnitSpline 1),
        le_abs_self Real.eulerMascheroniConstant, (abs_le.mp hself_err).1]
    have hconst_u :
        -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
          |Real.eulerMascheroniConstant| + 1) ≤
        (completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant +
          completeWeilSelfError tiltedUnitSpline c N) * ‖u‖ ^ 2 := by
      have hA0 : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| +
          |Real.eulerMascheroniConstant| + 1 := by positivity
      calc
        -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
            |Real.eulerMascheroniConstant| + 1) ≤
          -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
            |Real.eulerMascheroniConstant| + 1) * ‖u‖ ^ 2 := by
          nlinarith only [hA0, hu_sq_le1, sq_nonneg ‖u‖]
        _ ≤ _ := mul_le_mul_of_nonneg_right hconst_lb (sq_nonneg _)
    linarith only [hlc_u, hconst_u]
  have hcen := CompletedArithmeticForms.abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
    (completeWeilPoleShift tiltedUnitSpline c) hR' hR6N hlog hu hu1 hu1
  have hpole_le : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
    exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
  have hcen' :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫| ≤
        144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by
    have h1R0 : 0 ≤ (1 + Real.log R') / Real.sqrt (Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have h1 : 144 * |completeWeilPoleShift tiltedUnitSpline c| *
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤
      144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by
      calc
        144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) =
          144 * |completeWeilPoleShift tiltedUnitSpline c| *
            ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 144 * c * ((1 + Real.log R') / Real.sqrt (Real.log N)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hpole_le]) h1R0
        _ = 144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
    calc
      _ ≤ 144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) * ‖u‖ * ‖u‖ := hcen
      _ = (144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖u‖ ^ 2 := by ring
      _ ≤ 144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) * 1 :=
        mul_le_mul h1 hu_sq_le1 (sq_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hsep' :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫| ≤
        C_sep' * (c ^ 2 / Real.log N) := by
    have h1 := CompletedArithmeticForms.abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hR' hR4_N hlog hu
    calc
      _ ≤ C_sep' * c ^ 2 / Real.log N * ‖u‖ ^ 2 := h1
      _ = C_sep' * (c ^ 2 / Real.log N) * ‖u‖ ^ 2 := by ring
      _ ≤ C_sep' * (c ^ 2 / Real.log N) * 1 :=
        mul_le_mul_of_nonneg_left hu_sq_le1 (by positivity)
      _ = _ := mul_one _
  have hod' :
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, u⟫| ≤
        20 * C_od * (c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
    let d := Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
      downwardPrimeVector tiltedUnitSpline c N u
    let T := linearNearRowRadius c + 1
    let u_top : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
      WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
        if (N : ℝ) / (idx.1 : ℝ) < T then u.ofLp idx else 0)
    have hinner_eq : ⟪d, u⟫ = ⟪d, u_top⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
      refine Finset.sum_congr rfl fun idx _ => ?_
      change u.ofLp idx * d.ofLp idx =
        (if (N : ℝ) / (idx.1 : ℝ) < T then u.ofLp idx else 0) * d.ofLp idx
      by_cases hlt : (N : ℝ) / (idx.1 : ℝ) < T
      · rw [if_pos hlt]
      · rw [if_neg hlt, zero_mul]
        obtain ⟨hov0, hdn0⟩ := overlap_sub_downward_apply_eq_zero_of_quotient_ge
          contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hc1 hN1 hw1 u idx (le_of_not_gt hlt)
        have hd0 : d.ofLp idx = 0 := by
          change (Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u) idx -
            downwardPrimeVector tiltedUnitSpline c N u idx = 0
          rw [hov0, hdn0, sub_zero]
        rw [hd0, mul_zero]
    have hu_top_le1 : ‖u_top‖ ≤ 1 := by
      have hsq : ‖u_top‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        refine Finset.sum_le_sum fun idx _ => ?_
        change ‖if (N : ℝ) / (idx.1 : ℝ) < T then u.ofLp idx else 0‖ ^ 2 ≤ ‖u.ofLp idx‖ ^ 2
        split_ifs <;> simp [sq_nonneg]
      nlinarith only [hsq, hu_sq_le1, norm_nonneg u_top]
    have hu_top_log : ‖u_top‖ ≤ 10 * Real.sqrt ((1 + Real.log c) / Real.log N) := by
      have hT1 : 1 ≤ T := by dsimp only [T]; unfold linearNearRowRadius; positivity
      have hu_top_sum : ‖u_top‖ ^ 2 =
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
            primeHorizonExtension u n ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, sum_filter,
          ← sum_coe_sort (Icc 1 N) (fun n =>
            if (N : ℝ) / (n : ℝ) < T then primeHorizonExtension u n ^ 2 else 0)]
        refine Finset.sum_congr rfl fun idx _ => ?_
        change ‖if (N : ℝ) / (idx.1 : ℝ) < T then u.ofLp idx else 0‖ ^ 2 =
          if (N : ℝ) / (idx.1 : ℝ) < T then primeHorizonExtension u idx.1 ^ 2 else 0
        rw [primeHorizonExtension_coe u idx]
        split_ifs <;> simp [Real.norm_eq_abs, sq_abs]
      have htail := CompletedArithmeticForms.sum_quotient_tail_sq_le_of_mem_conductorSubspace
        hR' hT1 hRNT hlog hu
      rw [← hu_top_sum] at htail
      have h2T_pos : 0 < 2 * T := by linarith only [hT1]
      have hlog2T_nonneg : 0 ≤ Real.log (2 * T) + 3 := by
        have : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith only [hT1])
        linarith only [this]
      have he2 : Real.exp 2 ≤ 9 := by
        have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith only [he1, h2, Real.exp_pos 1]
      have h2T_le : 2 * T ≤ 38 * c := by
        dsimp only [T]; unfold linearNearRowRadius
        nlinarith only [hc1, he2]
      have hlog2T_le : 2 * (Real.log (2 * T) + 3) ≤ 100 * (1 + Real.log c) := by
        have h1 := Real.log_le_log h2T_pos h2T_le
        rw [Real.log_mul (by norm_num) hc0.ne'] at h1
        have h38 : Real.log 38 ≤ 37 := by
          linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 38)]
        have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
        linarith only [h1, h38, hlc0]
      have hL_prod : Real.log N * ‖u_top‖ ^ 2 ≤ 100 * (1 + Real.log c) := by
        calc
          Real.log N * ‖u_top‖ ^ 2 ≤ 2 * (Real.log (2 * T) + 3) * ‖u‖ ^ 2 := htail
          _ ≤ 2 * (Real.log (2 * T) + 3) * 1 := mul_le_mul_of_nonneg_left hu_sq_le1
            (by linarith only [hlog2T_nonneg])
          _ ≤ 100 * (1 + Real.log c) := by linarith only [hlog2T_le]
      have hdiv : ‖u_top‖ ^ 2 ≤ (10 * Real.sqrt ((1 + Real.log c) / Real.log N)) ^ 2 := by
        have h1 : ‖u_top‖ ^ 2 ≤ 100 * ((1 + Real.log c) / Real.log N) := by
          rw [mul_div_assoc, le_div_iff₀ hL0]
          linarith only [hL_prod]
        have hlc0 : 0 ≤ (1 + Real.log c) / Real.log N := by
          have := Real.log_nonneg hc1; positivity
        calc
          ‖u_top‖ ^ 2 ≤ 100 * ((1 + Real.log c) / Real.log N) := h1
          _ = (10 * Real.sqrt ((1 + Real.log c) / Real.log N)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hlc0]; ring
      have hrhs0 : 0 ≤ 10 * Real.sqrt ((1 + Real.log c) / Real.log N) := by positivity
      nlinarith only [hdiv, norm_nonneg u_top, hrhs0]
    have hd_norm : ‖d‖ ≤ C_od * (c ^ 2 * (1 + Real.log R') *
        Real.sqrt ((1 + Real.log c) / Real.log N) +
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
      have h1 := hod hR' hRR_N hlog hc1 hw1 hRNT hu
      have h0 : 0 ≤ C_od * (c ^ 2 * (1 + Real.log R') *
          Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
        have := Real.log_natCast_nonneg R'; positivity
      exact h1.trans ((mul_le_mul_of_nonneg_left hu_le1 h0).trans_eq (mul_one _))
    have hcs : |⟪d, u⟫| ≤ ‖d‖ * ‖u_top‖ := by
      rw [hinner_eq]; exact abs_real_inner_le_norm d u_top
    have hpart1 : (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N)) *
        ‖u_top‖ ≤ 10 * (c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N) := by
      have h1R0 : 0 ≤ c ^ 2 * (1 + Real.log R') := by
        have := Real.log_natCast_nonneg R'; positivity
      have hlc0 : 0 ≤ (1 + Real.log c) / Real.log N := by
        have := Real.log_nonneg hc1; positivity
      calc
        (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N)) * ‖u_top‖ ≤
            (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N)) *
              (10 * Real.sqrt ((1 + Real.log c) / Real.log N)) :=
          mul_le_mul_of_nonneg_left hu_top_log (by positivity)
        _ = 10 * (c ^ 2 * (1 + Real.log R')) *
              (Real.sqrt ((1 + Real.log c) / Real.log N) ^ 2) := by ring
        _ = 10 * (c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N) := by
          rw [Real.sq_sqrt hlc0]; ring
    have hpart2 : (c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u_top‖ ≤
        10 * (c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
      have h0 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
      calc
        _ ≤ (c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * 1 :=
          mul_le_mul_of_nonneg_left hu_top_le1 h0
        _ ≤ 10 * (c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by linarith only [h0]
    have hprod := (mul_le_mul_of_nonneg_right hd_norm (norm_nonneg u_top))
    have hcomb : C_od * (c ^ 2 * (1 + Real.log R') *
          Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u_top‖ ≤
        10 * C_od * (c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
      have hadd := add_le_add hpart1 hpart2
      have hm := mul_le_mul_of_nonneg_left hadd hC_od.le
      linarith [show C_od * (c ^ 2 * (1 + Real.log R') *
          Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u_top‖ =
        C_od * ((c ^ 2 * (1 + Real.log R') *
          Real.sqrt ((1 + Real.log c) / Real.log N)) * ‖u_top‖ +
          (c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u_top‖) by ring,
        show C_od * (10 * (c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N) +
          10 * (c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N))) =
        10 * C_od * (c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) by ring]
    dsimp only [d] at hcs hprod
    linarith only [hcs, hprod, hcomb]
  have hsum_err_le1 :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫| +
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫| +
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, u⟫| ≤ 1 := by
    have ht1 : 0 ≤ c * (1 + Real.log R') / Real.sqrt (Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have ht2 : 0 ≤ c ^ 2 / Real.log N := by positivity
    have ht3 : 0 ≤ c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
      have := Real.log_nonneg hc1; have := Real.log_natCast_nonneg R'; positivity
    have ht4 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
    dsimp only [C_err] at herr
    nlinarith only [hcen', hsep', hod', herr, ht1, ht2, ht3, ht4, hC_sep'0, hC_od]
  have hpole0 := CompletedArithmeticForms.fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
    tiltedUnitSpline c hN2 hu1 hu1
  have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc0 hN1 u
  rw [CompletedArithmeticForms.overlap_sub_nonRatio_inner_eq contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u, hpole0] at hdecomp
  change completeWeilEnergy tiltedUnitSpline c N u =
    renormalizedPrimeEnergy N u +
    (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
      completeWeilSelfError tiltedUnitSpline c N) * ‖u‖ ^ 2 +
    ⟪Matrix.toEuclideanLin
      (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫ -
    ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫ + 0 +
    (-⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ +
      2 * ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
        downwardPrimeVector tiltedUnitSpline c N u, u⟫) at hdecomp
  have habs_c := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫| ≤ _)).1
  have habs_s := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫| ≤ _)).2
  have habs_o := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (overlapMatrix tiltedUnitSpline c N) u -
    downwardPrimeVector tiltedUnitSpline c N u, u⟫| ≤ _)).1
  dsimp only [C_dec]
  linarith only [hdecomp, hself_term, hsum_err_le1, habs_c, habs_s, habs_o]

private theorem abs_add_three_le_local (x₁ x₂ x₃ : ℝ) :
    |x₁ + x₂ + x₃| ≤ |x₁| + |x₂| + |x₃| :=
  (abs_add_le (x₁ + x₂) x₃).trans (add_le_add (abs_add_le x₁ x₂) le_rfl)

private theorem mul_le_one_of_le_mul_le_one_local {A C T S : ℝ}
    (hA : A ≤ C) (hC0 : 0 ≤ C) (hT0 : 0 ≤ T) (hTS : T ≤ S) (hCS : C * S ≤ 1) :
    A * T ≤ 1 :=
  (mul_le_mul hA hTS hT0 hC0).trans hCS

private def lowBandPacket_local (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N

private def highBandCoeffs_local (Q₁ : ℕ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ≤ Q₁ then 0 else a m

private def highBandPacket_local (Q₁ R' N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 R', highBandCoeffs_local Q₁ a m • normalizedRamanujanHorizonVector m N

private def lowBandDiagPacket_local (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁,
    (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
      normalizedRamanujanHorizonVector m N

private def lowBandAdjPacket_local (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁,
    (a m * ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N

private theorem lowBand_highBand_packet_split_local {Q₁ R' N : ℕ} {a : ℕ → ℝ}
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hRR_N : R' * R' ≤ N)
    (hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N)
    (hu_eq : u = ∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N)
    (huQ : u ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2) (hu_le1 : ‖u‖ ≤ 1)
    (h1080 : 1080 * ((1 + Real.log R') / Real.log N) ≤ 1) :
    u = lowBandPacket_local Q₁ N a + highBandPacket_local Q₁ R' N a ∧
    lowBandPacket_local Q₁ N a ∈ conductorSubspace R' N ∧
    highBandPacket_local Q₁ R' N a ∈ conductorSubspace R' N ∧
    ‖lowBandPacket_local Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N ∧
    ‖lowBandPacket_local Q₁ N a‖ ≤ 1 / 20 ∧
    1 / 2 ≤ ‖highBandPacket_local Q₁ R' N a‖ ^ 2 ∧
    ‖highBandPacket_local Q₁ R' N a‖ ≤ 2 := by
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have huLow_R' : lowBandPacket_local Q₁ N a = ∑ m ∈ Icc 1 R',
      (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N := by
    unfold lowBandPacket_local
    have hsub : Icc 1 Q₁ ⊆ Icc 1 R' := Icc_subset_Icc le_rfl hQR'
    calc
      (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
          ∑ m ∈ Icc 1 Q₁,
            (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
      _ = _ := sum_subset hsub fun m hmR hmQ => by
        have hnot : ¬m ≤ Q₁ := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        rw [if_neg hnot, zero_smul]
  have hu_split : u = lowBandPacket_local Q₁ N a + highBandPacket_local Q₁ R' N a := by
    rw [hu_eq, huLow_R', highBandPacket_local]
    unfold highBandCoeffs_local
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have huLow_mem : lowBandPacket_local Q₁ N a ∈ conductorSubspace R' N := by
    unfold lowBandPacket_local
    exact conductorSubspace_mono hQR' N
      (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a)
  have hy_mem : highBandPacket_local Q₁ R' N a ∈ conductorSubspace R' N := by
    unfold highBandPacket_local
    exact sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R' N (highBandCoeffs_local Q₁ a)
  have huLow_bound : ‖lowBandPacket_local Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N := by
    have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q₁) hQR' hR'2 hRR_N
      hlog18_R' (hu_eq ▸ huQ)).2
    rw [← hu_eq, show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket_local Q₁ N a from rfl] at hlow
    have h0 : 0 ≤ 54 * (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    exact hlow.trans ((mul_le_mul_of_nonneg_left hu_le1 h0).trans_eq (mul_one _))
  have huLow_le20 : ‖lowBandPacket_local Q₁ N a‖ ≤ 1 / 20 := by
    have h54 : 54 * (1 + Real.log R') / Real.log N =
        54 * ((1 + Real.log R') / Real.log N) := by ring
    linarith only [huLow_bound, h1080, h54]
  have hy_bounds : 1 / 2 ≤ ‖highBandPacket_local Q₁ R' N a‖ ^ 2 ∧
      ‖highBandPacket_local Q₁ R' N a‖ ≤ 2 := by
    have hu_ge : 17 / 20 ≤ ‖u‖ := by nlinarith only [hu_sq_ge, norm_nonneg u]
    have htri1 : ‖u‖ ≤ ‖lowBandPacket_local Q₁ N a‖ + ‖highBandPacket_local Q₁ R' N a‖ := by
      rw [hu_split]; exact norm_add_le _ _
    have hy_ge : 4 / 5 ≤ ‖highBandPacket_local Q₁ R' N a‖ := by
      linarith only [hu_ge, htri1, huLow_le20]
    have hy_eq : highBandPacket_local Q₁ R' N a = u - lowBandPacket_local Q₁ N a := by
      rw [hu_split]; abel
    have htri2 : ‖highBandPacket_local Q₁ R' N a‖ ≤ ‖u‖ + ‖lowBandPacket_local Q₁ N a‖ := by
      rw [hy_eq]; exact norm_sub_le _ _
    exact ⟨by nlinarith only [hy_ge], by linarith only [htri2, hu_le1, huLow_le20]⟩
  exact ⟨hu_split, huLow_mem, hy_mem, huLow_bound, huLow_le20, hy_bounds.1, hy_bounds.2⟩

private theorem overlap_diff_of_conductor_split_local {R' N : ℕ} {c C_ov : ℝ}
    (_hC_ov : 0 < C_ov)
    (hov : ∀ {R₁ R₂ N : ℕ} {c : ℝ},
      2 ≤ R₁ → 2 ≤ R₂ →
      18 * (1 + Real.log R₁) ≤ Real.log N →
      18 * (1 + Real.log R₂) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      ((R₁ * R₁ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ((R₂ * R₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u v : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R₁ N → v ∈ conductorSubspace R₂ N →
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, v⟫| ≤
          C_ov * c * (1 + Real.log c) * ‖u‖ * ‖v‖)
    (hR'2 : 2 ≤ R') (hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N)
    (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hw1 : c / N ≤ 1 / 3)
    (hRNT : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N)
    {u v y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu_split : u = v + y)
    (hv_mem : v ∈ conductorSubspace R' N) (hy_mem : y ∈ conductorSubspace R' N)
    (hv_bound : ‖v‖ ≤ 54 * (1 + Real.log R') / Real.log N)
    (hv_le20 : ‖v‖ ≤ 1 / 20) (hy_le2 : ‖y‖ ≤ 2)
    (h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) ≤ 1) :
    |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ -
      ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, y⟫| ≤ 1 := by
  have hexp :
      ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ -
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, y⟫ =
      ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v, v⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v, y⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, v⟫ := by
    rw [hu_split, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  have h1 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hv_mem hv_mem
  have h2 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hv_mem hy_mem
  have h3 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hy_mem hv_mem
  have hnorm_sum : ‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖ ≤ 5 * ‖v‖ := by
    nlinarith only [hv_le20, hy_le2, norm_nonneg v]
  rw [hexp]
  calc
    |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v, v⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v, y⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, v⟫| ≤
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v, v⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v, y⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, v⟫| :=
      abs_add_three_le_local _ _ _
    _ ≤ C_ov * c * (1 + Real.log c) * (‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖) := by
      linarith only [h1, h2, h3]
    _ ≤ C_ov * c * (1 + Real.log c) * (5 * (54 * (1 + Real.log R') / Real.log N)) := by
      refine mul_le_mul_of_nonneg_left (hnorm_sum.trans (by linarith only [hv_bound])) ?_
      have := Real.log_nonneg hc1; positivity
    _ = 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) := by ring
    _ ≤ 1 := h270

private theorem lowBandPacket_prime_cross_le_local {Q₁ R' N : ℕ} {C_pr : ℝ} {a : ℕ → ℝ}
    (hC_pr : 0 < C_pr)
    (hpr_res : ∀ {M N : ℕ}, 2 ≤ M → M ^ 6 ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ a : ℕ → ℝ,
        ‖Matrix.toEuclideanLin (fullPrimeMatrix N)
            (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) -
          ∑ m ∈ Icc 1 M,
            (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
              normalizedRamanujanHorizonVector m N‖ ≤
          C_pr * (1 + (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)) *
            ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖)
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hQ6N : Q₁ ^ 6 ≤ N) (hQQ_N : Q₁ * Q₁ ≤ N)
    (hlog18_Q : 18 * (1 + Real.log Q₁) ≤ Real.log N)
    (ht2_1 : (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N) ≤ 1)
    (h864 : 864 * ((1 + Real.log R') ^ 2 / Real.log N) ≤ 1)
    (h432 : 432 * C_pr * ((1 + Real.log R') / Real.log N) ≤ 1)
    (huLow_bound : ‖lowBandPacket_local Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N)
    {y : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hy_le2 : ‖y‖ ≤ 2) :
    2 * |⟪Real.log N • lowBandPacket_local Q₁ N a -
      Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a), y⟫| ≤ 2 := by
  have hlog_Q_le_R' : Real.log Q₁ ≤ Real.log R' :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q₁ by omega)) (by exact_mod_cast hQR')
  have hid : Real.log N • lowBandPacket_local Q₁ N a -
        Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) =
      lowBandAdjPacket_local Q₁ N a -
        (Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
          lowBandDiagPacket_local Q₁ N a) := by
    have hsub : Real.log N • lowBandPacket_local Q₁ N a - lowBandDiagPacket_local Q₁ N a =
        lowBandAdjPacket_local Q₁ N a := by
      unfold lowBandPacket_local lowBandDiagPacket_local lowBandAdjPacket_local
      rw [Finset.smul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [smul_smul, ← sub_smul]
      congr 1; ring
    rw [← hsub]; abel
  have hadj_norm : ‖lowBandAdjPacket_local Q₁ N a‖ ≤
      4 * (1 + Real.log R') * ‖lowBandPacket_local Q₁ N a‖ := by
    have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
      rw [abs_le]
      have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 0
      simp [Real.eulerMascheroniSeq] at h1
      exact ⟨by linarith, by linarith [Real.eulerMascheroniConstant_lt_two_thirds]⟩
    have hadj_m : ∀ m ∈ Icc 1 Q₁, |ramanujanAdjunctionEnergy m| ≤ 2 * (1 + Real.log R') := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hlm0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
      have hlmR : Real.log m ≤ Real.log R' :=
        (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmQ)).trans hlog_Q_le_R'
      have htd0 := tameDifferent_nonneg m
      have htd := (CompletedArithmeticForms.tameDifferent_le_log hm1).trans hlmR
      unfold ramanujanAdjunctionEnergy
      exact (abs_add_le _ _).trans (by
        rw [abs_of_nonneg (add_nonneg hlm0 htd0)]
        linarith only [hγ, hlmR, htd])
    have hadj_sq : (∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) ^ 2) ≤
        (2 * (1 + Real.log R')) ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hsq := pow_le_pow_left₀ (abs_nonneg _) (hadj_m m hm) 2
      rw [sq_abs] at hsq
      nlinarith only [hsq, sq_nonneg (a m)]
    have hru_lo := (half_and_three_halves_riesz_of_log_le hQ₁ hQQ_N hlog18_Q a).1
    have hru_hi := (half_and_three_halves_riesz_of_log_le hQ₁ hQQ_N hlog18_Q
      (fun m => a m * ramanujanAdjunctionEnergy m)).2
    rw [show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket_local Q₁ N a from rfl] at hru_lo
    rw [show (∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) •
      normalizedRamanujanHorizonVector m N) = lowBandAdjPacket_local Q₁ N a from rfl] at hru_hi
    have hnorm_sq : ‖lowBandAdjPacket_local Q₁ N a‖ ^ 2 ≤
        (4 * (1 + Real.log R') * ‖lowBandPacket_local Q₁ N a‖) ^ 2 := by
      calc
        ‖lowBandAdjPacket_local Q₁ N a‖ ^ 2 ≤ (3 / 2 : ℝ) *
            ∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) ^ 2 := hru_hi
        _ ≤ (3 / 2 : ℝ) * ((2 * (1 + Real.log R')) ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2) :=
          mul_le_mul_of_nonneg_left hadj_sq (by norm_num)
        _ ≤ (3 / 2 : ℝ) * ((2 * (1 + Real.log R')) ^ 2 * (2 * ‖lowBandPacket_local Q₁ N a‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith only [hru_lo]) (sq_nonneg _)) (by norm_num)
        _ ≤ (4 * (1 + Real.log R') * ‖lowBandPacket_local Q₁ N a‖) ^ 2 := by
          nlinarith only [sq_nonneg ((1 + Real.log R') * ‖lowBandPacket_local Q₁ N a‖)]
    have hrhs0 : 0 ≤ 4 * (1 + Real.log R') * ‖lowBandPacket_local Q₁ N a‖ := by
      have := Real.log_natCast_nonneg R'; positivity
    nlinarith only [hnorm_sq, norm_nonneg (lowBandAdjPacket_local Q₁ N a), hrhs0]
  have hres_norm :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
        lowBandDiagPacket_local Q₁ N a‖ ≤ 2 * C_pr * ‖lowBandPacket_local Q₁ N a‖ := by
    have h1 := hpr_res hQ₁ hQ6N hlog18_Q a
    rw [show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket_local Q₁ N a from rfl,
      show (∑ m ∈ Icc 1 Q₁, (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
        normalizedRamanujanHorizonVector m N) = lowBandDiagPacket_local Q₁ N a from rfl] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hC_pr, ht2_1]) (norm_nonneg _))
  have hadj_part : 2 * |⟪lowBandAdjPacket_local Q₁ N a, y⟫| ≤ 1 := by
    calc
      2 * |⟪lowBandAdjPacket_local Q₁ N a, y⟫| ≤ 2 * (‖lowBandAdjPacket_local Q₁ N a‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
      _ ≤ 2 * ((4 * (1 + Real.log R') * (54 * (1 + Real.log R') / Real.log N)) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul
          (hadj_norm.trans (mul_le_mul_of_nonneg_left huLow_bound
            (by have := Real.log_natCast_nonneg R'; positivity)))
          hy_le2 (norm_nonneg y) (by have := Real.log_natCast_nonneg R'; positivity)
      _ = 864 * ((1 + Real.log R') ^ 2 / Real.log N) := by ring
      _ ≤ 1 := h864
  have hres_part :
      2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
        lowBandDiagPacket_local Q₁ N a, y⟫| ≤ 1 := by
    calc
      2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
          lowBandDiagPacket_local Q₁ N a, y⟫| ≤
          2 * (‖Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
            lowBandDiagPacket_local Q₁ N a‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
      _ ≤ 2 * ((2 * C_pr * (54 * (1 + Real.log R') / Real.log N)) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul
          (hres_norm.trans (mul_le_mul_of_nonneg_left huLow_bound (by positivity)))
          hy_le2 (norm_nonneg y) (by have := Real.log_natCast_nonneg R'; positivity)
      _ = 432 * C_pr * ((1 + Real.log R') / Real.log N) := by ring
      _ ≤ 1 := h432
  rw [hid, inner_sub_left]
  calc
    2 * |⟪lowBandAdjPacket_local Q₁ N a, y⟫ -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
          lowBandDiagPacket_local Q₁ N a, y⟫| ≤
        2 * |⟪lowBandAdjPacket_local Q₁ N a, y⟫| +
          2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
            lowBandDiagPacket_local Q₁ N a, y⟫| := by
      linarith only [abs_sub ⟪lowBandAdjPacket_local Q₁ N a, y⟫
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a) -
          lowBandDiagPacket_local Q₁ N a, y⟫]
    _ ≤ 2 := by linarith only [hadj_part, hres_part]

private theorem highBandPacket_prime_and_overlap_bounds_local
    {Q₁ R' N : ℕ} {c C_mid C_prime : ℝ} {a : ℕ → ℝ}
    (hmid : ∀ {Q₁ Q₂ N : ℕ} {c : ℝ},
      2 ≤ Q₁ → Q₁ ≤ Q₂ → Q₂ * Q₂ ≤ N →
      18 * (1 + Real.log Q₂) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((Q₂ * Q₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {a : ℕ → ℝ}, (∀ m ∈ Icc 1 Q₁, a m = 0) →
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 Q₂, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q₂, a m • normalizedRamanujanHorizonVector m N⟫| ≤
          C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
            c ^ 5 * Real.log N / N +
            c ^ 4 / Real.sqrt Q₁ +
            c ^ 3 * (Q₂ : ℝ) ^ 4 / N) *
          ‖∑ m ∈ Icc 1 Q₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)
    (hC_prime : 0 < C_prime)
    (hprime : (Real.log Q₁ / 2 - C_prime) * ‖highBandPacket_local Q₁ R' N a‖ ^ 2 ≤
      renormalizedPrimeEnergy N (highBandPacket_local Q₁ R' N a))
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hRR_N : R' * R' ≤ N)
    (hlog36 : 36 * (1 + Real.log R') ≤ Real.log N)
    (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hw1 : c / N ≤ 1 / 3)
    (hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N)
    (hRNT : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N)
    (hmid_le1 : C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
      c ^ 5 * Real.log N / N + c ^ 4 / Real.sqrt Q₁ + c ^ 3 * (R' : ℝ) ^ 4 / N) ≤ 1)
    (hy_sq_ge : 1 / 2 ≤ ‖highBandPacket_local Q₁ R' N a‖ ^ 2)
    (hy_le2 : ‖highBandPacket_local Q₁ R' N a‖ ≤ 2) :
    |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N)
        (highBandPacket_local Q₁ R' N a), highBandPacket_local Q₁ R' N a⟫| ≤ 4 ∧
    (1 / 4) * Real.log Q₁ - 4 * C_prime ≤
      renormalizedPrimeEnergy N (highBandPacket_local Q₁ R' N a) := by
  have hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have ha0 : ∀ m ∈ Icc 1 Q₁, highBandCoeffs_local Q₁ a m = 0 := fun m hm => by
    unfold highBandCoeffs_local; exact if_pos (mem_Icc.mp hm).2
  have hov_y :
      |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N)
          (highBandPacket_local Q₁ R' N a), highBandPacket_local Q₁ R' N a⟫| ≤ 4 := by
    have hm := hmid hQ₁ hQR' hRR_N hlog18_R' hc1 hcL hw1 hradN hRNT ha0
    rw [show (∑ m ∈ Icc 1 R', highBandCoeffs_local Q₁ a m • normalizedRamanujanHorizonVector m N) =
      highBandPacket_local Q₁ R' N a from rfl] at hm
    have hy_sq4 : ‖highBandPacket_local Q₁ R' N a‖ ^ 2 ≤ 4 := by
      nlinarith only [hy_le2, norm_nonneg (highBandPacket_local Q₁ R' N a)]
    calc
      |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N)
          (highBandPacket_local Q₁ R' N a), highBandPacket_local Q₁ R' N a⟫| ≤
          C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
            c ^ 5 * Real.log N / N + c ^ 4 / Real.sqrt Q₁ +
            c ^ 3 * (R' : ℝ) ^ 4 / N) * ‖highBandPacket_local Q₁ R' N a‖ ^ 2 := hm
      _ ≤ 1 * 4 := mul_le_mul hmid_le1 hy_sq4 (sq_nonneg _) zero_le_one
      _ = 4 := one_mul 4
  have hprime_y :
      (1 / 4) * Real.log Q₁ - 4 * C_prime ≤
        renormalizedPrimeEnergy N (highBandPacket_local Q₁ R' N a) := by
    have hy_sq4 : ‖highBandPacket_local Q₁ R' N a‖ ^ 2 ≤ 4 := by
      nlinarith only [hy_le2, norm_nonneg (highBandPacket_local Q₁ R' N a)]
    have hlead := mul_le_mul_of_nonneg_left hy_sq_ge
      (div_nonneg (Real.log_natCast_nonneg Q₁) zero_le_two)
    have hloss := mul_le_mul_of_nonneg_left hy_sq4 hC_prime.le
    nlinarith only [hprime, hlead, hloss]
  exact ⟨hov_y, hprime_y⟩

/-- **Sharpened coercivity above `Q₁`.**
Uses `exists_completeWeilEnergy_ge_prime_sub_overlap_sharpened` so the `(overlap - downward)`
quadratic error has denominator `log N` instead of `√(log N)`, removing the `19 * α < 1 / 2` cap. -/
private theorem exists_high_band_coercivity_sharpened :
    ∃ C_coerc C_small : ℝ, 0 < C_coerc ∧ 0 < C_small ∧
      ∀ {Q₁ R' N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R' → R' ^ 6 ≤ N → 36 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_small * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          ((1 + Real.log R') ^ 2 / Real.log N + (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) +
          c * (1 + Real.log R') / Real.sqrt (Real.log N) +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N +
          c ^ 4 / Real.sqrt Q₁ +
          c ^ 3 * (R' : ℝ) ^ 4 / N +
          c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace Q₁ N)ᗮ →
        3 / 4 ≤ ‖u‖ ^ 2 → ‖u‖ ≤ 1 →
        (1 / 4) * Real.log Q₁ - Real.log c - C_coerc ≤
          completeWeilEnergy tiltedUnitSpline c N u := by
  obtain ⟨C_dec, C_err, hC_dec, hC_err, hdec⟩ :=
    exists_completeWeilEnergy_ge_prime_sub_overlap_sharpened
  obtain ⟨C_ov, hC_ov, hov⟩ :=
    CompletedArithmeticForms.exists_overlapMatrix_inner_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_pr, hC_pr, hpr_res⟩ :=
    CompletedArithmeticForms.exists_fullPrimeMatrix_packet_residual_norm_le
  obtain ⟨C_mid, hC_mid, hmid⟩ :=
    CompletedArithmeticForms.exists_overlapMatrix_midBand_inner_le
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_prime, hC_prime, hprime⟩ :=
    CompletedArithmeticForms.exists_primePacket_energy_ge_log
  have hlog4_0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C_dec + (Real.log 4 + 4) + 8 + 4 * C_prime,
    C_err + 1080 + 270 * C_ov + 864 + 432 * C_pr + C_mid + 1,
    by positivity, by positivity, ?_⟩
  intro Q₁ R' N c hQ₁ hQR' hR6N hlog36 hc1 hcL hw1 hradN hRNT hsmall
    u hu huQ hu_sq_ge hu_le1
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hQ6N : Q₁ ^ 6 ≤ N := (Nat.pow_le_pow_left hQR' 6).trans hR6N
  have hQQ_N : Q₁ * Q₁ ≤ N := (Nat.mul_le_mul hQR' hQR').trans hRR_N
  have hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have hlog_Q_le_R' : Real.log Q₁ ≤ Real.log R' :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q₁ by omega)) (by exact_mod_cast hQR')
  have hlog18_Q : 18 * (1 + Real.log Q₁) ≤ Real.log N := by
    linarith only [hlog18_R', hlog_Q_le_R']
  have hu1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    huQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have ht1 : 0 ≤ c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have := Real.log_nonneg hc1; have := Real.log_natCast_nonneg R'; positivity
  have ht2 : 0 ≤ ((1 + Real.log R') ^ 2 / Real.log N +
      (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) := by positivity
  have ht3 : 0 ≤ c * (1 + Real.log R') / Real.sqrt (Real.log N) := by
    have := Real.log_natCast_nonneg R'; positivity
  have ht4 : 0 ≤ c ^ 2 / Real.log N := by
    have := Real.log_natCast_nonneg N; positivity
  have ht5 : 0 ≤ c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have := Real.log_nonneg hc1; have := Real.log_natCast_nonneg R'; positivity
  have ht6 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
  have ht7 : 0 ≤ c ^ 5 * Real.log N / N := by
    have := Real.log_natCast_nonneg N; positivity
  have ht8 : 0 ≤ c ^ 4 / Real.sqrt Q₁ := by positivity
  have ht9 : 0 ≤ c ^ 3 * (R' : ℝ) ^ 4 / N := by positivity
  have ht10 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by
    have := Real.log_nonneg hc1; positivity
  have h1R_div_le : (1 + Real.log R') / Real.log N ≤
      c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have h1cc : 1 ≤ c * (1 + Real.log c) := by
      have := Real.log_nonneg hc1; nlinarith only [hc1, this]
    have h1R0 : 0 ≤ (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    calc
      (1 + Real.log R') / Real.log N = 1 * ((1 + Real.log R') / Real.log N) := (one_mul _).symm
      _ ≤ (c * (1 + Real.log c)) * ((1 + Real.log R') / Real.log N) :=
        mul_le_mul_of_nonneg_right h1cc h1R0
      _ = _ := by ring
  have h1R_sq_div : (1 + Real.log R') ^ 2 / Real.log N ≤
      ((1 + Real.log R') ^ 2 / Real.log N + (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) :=
    le_add_of_nonneg_right (by positivity)
  have hC0 : 0 ≤ C_err + 1080 + 270 * C_ov + 864 + 432 * C_pr + C_mid + 1 := by positivity
  have h1R0 : 0 ≤ (1 + Real.log R') / Real.log N := by
    have := Real.log_natCast_nonneg R'; positivity
  have herr_dec : C_err * (c * (1 + Real.log R') / Real.sqrt (Real.log N) +
      c ^ 2 / Real.log N +
      c ^ 2 * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
      c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 :=
    mul_le_one_of_le_mul_le_one_local
      (by linarith only [hC_ov, hC_pr, hC_mid]) hC0
      (by linarith only [ht3, ht4, ht5, ht6])
      (by linarith only [ht1, ht2, ht7, ht8, ht9, ht10]) hsmall
  have h1080 : 1080 * ((1 + Real.log R') / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one_local
      (by linarith only [hC_err, hC_ov, hC_pr, hC_mid]) hC0 h1R0
      (by linarith only [h1R_div_le, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one_local
      (by linarith only [hC_err, hC_pr, hC_mid]) hC0 ht1
      (by linarith only [ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have ht2_1 : (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N) ≤ 1 := by
    have hboth : ((1 + Real.log R') ^ 2 / Real.log N +
        (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) ≤ 1 := by
      simpa only [one_mul] using mul_le_one_of_le_mul_le_one_local (A := 1)
        (by linarith only [hC_err, hC_ov, hC_pr, hC_mid]) hC0 ht2
        (by linarith only [ht1, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
    exact (le_add_of_nonneg_left (by positivity)).trans hboth
  have h864 : 864 * ((1 + Real.log R') ^ 2 / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one_local
      (by linarith only [hC_err, hC_ov, hC_pr, hC_mid]) hC0 (by positivity)
      (by linarith only [h1R_sq_div, ht1, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have h432 : 432 * C_pr * ((1 + Real.log R') / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one_local
      (by linarith only [hC_err, hC_ov, hC_mid]) hC0 h1R0
      (by linarith only [h1R_div_le, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have hmid_le1 : C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
      c ^ 5 * Real.log N / N + c ^ 4 / Real.sqrt Q₁ + c ^ 3 * (R' : ℝ) ^ 4 / N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one_local
      (by linarith only [hC_err, hC_ov, hC_pr]) hC0
      (by linarith only [ht10, ht7, ht8, ht9])
      (by linarith only [ht1, ht2, ht3, ht4, ht5, ht6]) hsmall
  have hbase_dec := hdec hR'2 hR6N hlog18_R' hc1 hw1 hRNT herr_dec hu hu1 hu_le1
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R') (N := N) (x := u)).mp hu
  obtain ⟨hu_split, huLow_mem, hy_mem, huLow_bound, huLow_le20, hy_sq_ge, hy_le2⟩ :=
    lowBand_highBand_packet_split_local hQ₁ hQR' hRR_N hlog18_R' hu_eq huQ hu_sq_ge hu_le1 h1080
  have hov_diff := overlap_diff_of_conductor_split_local hC_ov hov hR'2 hlog18_R' hc1 hcL hw1 hRNT
    hu_split huLow_mem hy_mem huLow_bound huLow_le20 hy_le2 h270
  have hprime_uLow :
      -(Real.log 4 + 4) ≤ renormalizedPrimeEnergy N (lowBandPacket_local Q₁ N a) := by
    have hp := poleDefect_le_primeEnergy_add_row_cost (lowBandPacket_local Q₁ N a)
    have hd0 := poleDefect_nonneg N (primeHorizonExtension (lowBandPacket_local Q₁ N a))
    have huL_sq1 : ‖lowBandPacket_local Q₁ N a‖ ^ 2 ≤ 1 := by
      nlinarith only [huLow_le20, norm_nonneg (lowBandPacket_local Q₁ N a)]
    nlinarith only [hp, hd0, huL_sq1, hlog4_0]
  have hprime_cross := lowBandPacket_prime_cross_le_local hC_pr hpr_res hQ₁ hQR' hQ6N hQQ_N
    hlog18_Q ht2_1 h864 h432 huLow_bound hy_le2
  have hpacket_prime :
      (Real.log Q₁ / 2 - C_prime) * ‖highBandPacket_local Q₁ R' N a‖ ^ 2 ≤
        renormalizedPrimeEnergy N (highBandPacket_local Q₁ R' N a) :=
    hprime hQ₁ hQR' hRR_N hlog18_R' (highBandCoeffs_local Q₁ a)
      (fun m hm => by unfold highBandCoeffs_local; exact if_pos (mem_Icc.mp hm).2)
  obtain ⟨hov_y, hprime_y⟩ := highBandPacket_prime_and_overlap_bounds_local hmid hC_prime
    hpacket_prime hQ₁ hQR' hRR_N hlog36 hc1 hcL hw1 hradN hRNT hmid_le1 hy_sq_ge hy_le2
  have hprime_u :
      (1 / 4) * Real.log Q₁ - 4 * C_prime -
        (Real.log 4 + 4) - 2 ≤ renormalizedPrimeEnergy N u := by
    have hexp := renormalizedPrimeEnergy_add_eq_local
      (lowBandPacket_local Q₁ N a) (highBandPacket_local Q₁ R' N a)
    rw [← hu_split] at hexp
    have hcr_lb : -2 ≤ 2 * ⟪Real.log N • lowBandPacket_local Q₁ N a -
        Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a),
        highBandPacket_local Q₁ R' N a⟫ := by
      linarith only [neg_abs_le ⟪Real.log N • lowBandPacket_local Q₁ N a -
        Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket_local Q₁ N a),
        highBandPacket_local Q₁ R' N a⟫, hprime_cross]
    linarith only [hexp, hprime_uLow, hprime_y, hcr_lb]
  have hov_u : ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ ≤ 5 := by
    linarith only [(abs_le.mp hov_diff).2, (abs_le.mp hov_y).2]
  linarith only [hbase_dec, hprime_u, hov_u]


/-! ### Asymptotic parameter discharge (`α < 2 / 71`) and main Section 3 theorems -/

private theorem add_pow_four_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 4 ≤ 16 * x ^ 4 + 16 * y ^ 4 := by
  rcases le_total x y with hxy | hyx
  · calc
      (x + y) ^ 4 ≤ (2 * y) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith only [hxy]) 4
      _ = 16 * y ^ 4 := by ring
      _ ≤ 16 * x ^ 4 + 16 * y ^ 4 := le_add_of_nonneg_left (by positivity)
  · calc
      (x + y) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith only [hyx]) 4
      _ = 16 * x ^ 4 := by ring
      _ ≤ 16 * x ^ 4 + 16 * y ^ 4 := le_add_of_nonneg_right (by positivity)

private theorem add_pow_five_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 5 ≤ 32 * x ^ 5 + 32 * y ^ 5 := by
  rcases le_total x y with hxy | hyx
  · calc
      (x + y) ^ 5 ≤ (2 * y) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith only [hxy]) 5
      _ = 32 * y ^ 5 := by ring
      _ ≤ 32 * x ^ 5 + 32 * y ^ 5 := le_add_of_nonneg_left (by positivity)
  · calc
      (x + y) ^ 5 ≤ (2 * x) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith only [hyx]) 5
      _ = 32 * x ^ 5 := by ring
      _ ≤ 32 * x ^ 5 + 32 * y ^ 5 := le_add_of_nonneg_right (by positivity)

private theorem eventually_floor_log_rpow_bounds_sharpened {q : ℝ} (hq : 0 < q) (hqmax : q ≤ 6 / 25) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      2 ≤ Q₁ ∧
      (Q₁ : ℝ) ≤ L ^ q ∧
      (1 / 4 : ℝ) * L ^ q ≤ (Q₁ : ℝ) ∧
      q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) ∧
      Q₁ ^ 4 ≤ N := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp hLlim
  filter_upwards [hQlim.eventually_ge_atTop 4,
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 2] with N hX4 hL1 hN2
  dsimp only
  let L := Real.log (N : ℝ)
  let Xq := L ^ q
  let Q₁ := ⌊Xq⌋₊
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ Xq by linarith only [hX4]))
  have hQ_le : (Q₁ : ℝ) ≤ Xq := Nat.floor_le (by linarith only [hX4])
  have hQ_gt : Xq - 1 < (Q₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one Xq)
  have hQ_quarter : (1 / 4 : ℝ) * Xq ≤ (Q₁ : ℝ) := by linarith only [hX4, hQ_gt]
  have hQ_half : (1 / 2 : ℝ) * Xq ≤ (Q₁ : ℝ) := by linarith only [hX4, hQ_gt]
  have hlogQ_lb : q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hXq_pos : 0 < Xq := by linarith only [hX4]
    have h1 := Real.log_le_log (by positivity) hQ_half
    rw [Real.log_mul (by norm_num) hXq_pos.ne', one_div, Real.log_inv,
      show Xq = L ^ q from rfl, Real.log_rpow hL0] at h1
    linarith only [h1, hlog2]
  have hQ4_N : Q₁ ^ 4 ≤ N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 4
    have he : Xq ^ (4 : ℕ) = L ^ (4 * q) := by
      dsimp only [Xq]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1; ring
    have hL_le : L ^ (4 * q) ≤ L := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hqmax] : 4 * q ≤ 1)
    have hLN : L ≤ (N : ℝ) :=
      (Real.log_le_sub_one_of_pos hN0).trans (by linarith only)
    exact_mod_cast ((hp.trans_eq he).trans hL_le).trans hLN
  exact ⟨hQ2, hQ_le, hQ_quarter, hlogQ_lb, hQ4_N⟩

private theorem rpow_horizon_N_bounds_local {N R' : ℕ} {c H_res : ℝ}
    (hN1 : 1 ≤ N) (hR'2 : 2 ≤ R') (hc1 : 1 ≤ c) (_hH0 : 0 < H_res)
    (hL2000 : 2000 ≤ Real.log (N : ℝ)) (hHL : H_res ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ)) :
    H_res * c ^ 8 ≤ (N : ℝ) ∧
    4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
    c / (N : ℝ) ≤ 1 / 3 ∧
    4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 5 * Real.log (N : ℝ) / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) := by
  let L := Real.log (N : ℝ)
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL2000]
  have hX2000 : 2000 ≤ X := hL2000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX2000]
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcX : c ≤ X := hcL.trans hLX
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ k : ℕ, k ≤ 36 → X ^ k ≤ (N : ℝ) := fun k hk =>
    (pow_le_pow_right₀ hX1 hk).trans_eq hX36
  have hR'X : (R' : ℝ) ≤ X := by
    have hR'0 : (0 : ℝ) < R' := by exact_mod_cast (show 0 < R' by omega)
    have hlog_le : Real.log (R' : ℝ) ≤ Real.log X := by
      have h1 : Real.log X = (1 / 36 : ℝ) * Real.log (N : ℝ) := Real.log_rpow hN0 (1 / 36 : ℝ)
      linarith only [hlog36, h1]
    exact (Real.exp_log hR'0).symm.trans_le ((Real.exp_le_exp.mpr hlog_le).trans_eq (Real.exp_log hX0))
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [he1, h2, Real.exp_pos 1]
  have hlin_le : linearNearRowRadius c + 1 ≤ 19 * X := by
    unfold linearNearRowRadius; nlinarith only [hc1, hcX, he2]
  have hup_le : c * Real.exp 1 + 1 ≤ 4 * X := by nlinarith only [hc0, hc1, hcX, he1]
  have hRR1_le : ((R' * R' : ℕ) + 1 : ℝ) ≤ 2 * X ^ 2 := by
    have hR1 : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
    push_cast
    have hsq : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hR'X 2
    have h1sq : (1 : ℝ) ≤ (R' : ℝ) ^ 2 := one_le_pow₀ hR1
    linarith only [hsq, h1sq]
  have h1 : H_res * c ^ 8 ≤ (N : ℝ) := by
    have hHX : H_res ≤ X := hHL.trans hLX
    have hc8 : c ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hc0.le hcX 8
    calc
      H_res * c ^ 8 ≤ X * X ^ 8 := mul_le_mul hHX hc8 (by positivity) hX0.le
      _ = X ^ 9 := by ring
      _ ≤ (N : ℝ) := hpowX 9 (by norm_num)
  have h2 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have hconst : 4 * (Real.exp 1 + 3) ^ 2 ≤ X := by
      have : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
      linarith only [this, hX2000]
    calc
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ X * X ^ 2 :=
        mul_le_mul hconst hc2 (by positivity) hX0.le
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h3 : c / (N : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    have h3X : 3 * c ≤ X ^ 2 := by nlinarith only [hcX, hX2000]
    exact (by linarith only [h3X] : c * 3 ≤ X ^ 2).trans
      (by simpa only [one_mul] using hpowX 2 (by norm_num))
  have h4 : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    have hsq : (linearNearRowRadius c + 1) ^ 2 ≤ (19 * X) ^ 2 :=
      pow_le_pow_left₀ (by unfold linearNearRowRadius; positivity) hlin_le 2
    have h1444 : 1444 * X ^ 2 ≤ X ^ 3 := by nlinarith only [hX2000, sq_nonneg X]
    calc
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ 4 * (19 * X) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1444 * X ^ 2 := by ring
      _ ≤ X ^ 3 := h1444
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h5 : R' ^ 6 ≤ N := by
    have hR6 : (R' : ℝ) ^ 6 ≤ (N : ℝ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 6).trans (hpowX 6 (by norm_num))
    exact_mod_cast hR6
  have h6 : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) := by
    have h38 : 38 * X ^ 3 ≤ X ^ 4 := by
      calc
        38 * X ^ 3 ≤ X * X ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith only [hX2000]) (by positivity)
        _ = X ^ 4 := by ring
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (2 * X ^ 2) * (19 * X) :=
        mul_le_mul hRR1_le hlin_le (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = 38 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h38
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h7 : ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) := by
    have h8 : 8 * X ^ 3 ≤ X ^ 4 := by nlinarith only [hX2000, pow_nonneg hX0.le 3]
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (2 * X ^ 2) * (4 * X) :=
        mul_le_mul hRR1_le hup_le (by positivity) (by positivity)
      _ = 8 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h8
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h8 : (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 1 / L := by
    have hprod : (R' : ℝ) ^ 2 * L ^ 3 ≤ (N : ℝ) := by
      have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
      have hL3 : L ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hL0.le hLX 3
      calc
        (R' : ℝ) ^ 2 * L ^ 3 ≤ X ^ 2 * X ^ 3 := mul_le_mul hR2 hL3 (by positivity) (by positivity)
        _ = X ^ 5 := by ring
        _ ≤ (N : ℝ) := hpowX 5 (by norm_num)
    have hsq : ((R' : ℝ) * Real.sqrt (L / (N : ℝ))) ^ 2 ≤ (1 / L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), one_div, inv_pow, ← one_div]
      rw [← mul_div_assoc, div_le_div_iff₀ hN0 (sq_pos_of_pos hL0)]
      calc
        (R' : ℝ) ^ 2 * L * L ^ 2 = (R' : ℝ) ^ 2 * L ^ 3 := by ring
        _ ≤ 1 * (N : ℝ) := by rw [one_mul]; exact hprod
    have hlhs0 : 0 ≤ (R' : ℝ) * Real.sqrt (L / (N : ℝ)) := by positivity
    have hrhs0 : 0 ≤ 1 / L := by positivity
    nlinarith only [hsq, hlhs0, hrhs0]
  have h9 : c ^ 5 * L / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc5 : c ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ hc0.le hcX 5
    have hL2 : L ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hL0.le hLX 2
    calc
      c ^ 5 * L * L = c ^ 5 * L ^ 2 := by ring
      _ ≤ X ^ 5 * X ^ 2 := mul_le_mul hc5 hL2 (by positivity) (by positivity)
      _ = X ^ 7 := by ring
      _ ≤ (N : ℝ) := hpowX 7 (by norm_num)
  have h10 : c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc3 : c ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hc0.le hcX 3
    have hR4 : (R' : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 4
    calc
      c ^ 3 * (R' : ℝ) ^ 4 * L ≤ (X ^ 3 * X ^ 4) * X :=
        mul_le_mul (mul_le_mul hc3 hR4 (by positivity) (by positivity)) hLX hL0.le (by positivity)
      _ = X ^ 8 := by ring
      _ ≤ (N : ℝ) := hpowX 8 (by norm_num)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

private theorem rpow_horizon_L_smallness_bounds_sharpened
    {Q₁ R' N : ℕ} {c C_R C_pdef b_res C_small H_res α q ν : ℝ}
    (hα_71 : α ≤ 2 / 71) (h71_gap : 71 * α - 2 ≤ -4 * ν)
    (hqmax : q ≤ 6 / 25)
    (hν : 0 < ν) (hν1000 : ν ≤ 1 / 1000) (hsep : 4 * α - q / 2 ≤ -ν)
    (hN1 : 1 ≤ N) (hQ₁2 : 2 ≤ Q₁) (hQR' : Q₁ ≤ R')
    (hc1 : 1 ≤ c) (hCR0 : 0 < C_R) (hC_pdef1 : 1 ≤ C_pdef)
    (hb_res : 0 < b_res) (hCsmall0 : 0 < C_small) (hH0 : 0 < H_res)
    (hL2000 : 2000 ≤ Real.log (N : ℝ))
    (hHL : H_res ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hL43 : 36 ≤ Real.log (N : ℝ) ^ (43 / 80 : ℝ))
    (hCR_L : C_R + 2 ≤ Real.log (N : ℝ) ^ (1 / 400 : ℝ))
    (hbig_ν : 64 * C_R ^ 5 + 64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17) +
      20 * C_small + 64 ≤ Real.log (N : ℝ) ^ ν)
    (hQ_le : (Q₁ : ℝ) ≤ Real.log (N : ℝ) ^ q)
    (hQ_quarter : (1 / 4 : ℝ) * Real.log (N : ℝ) ^ q ≤ (Q₁ : ℝ))
    (hcα : c ≤ Real.log (N : ℝ) ^ α)
    (hR'_log : Real.log (R' : ℝ) ≤ C_R * c ^ 16 + Real.log (Q₁ : ℝ)) :
    c ≤ Real.log (N : ℝ) ∧
    36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    18 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (1 + Real.log (R' : ℝ)) / Real.sqrt (Real.log (N : ℝ)) ≤ 1 ∧
    (1 + Real.log (R' : ℝ)) ^ 2 * Real.sqrt (1 + Real.log (R' : ℝ)) / Real.log (N : ℝ) ≤
      c ^ 4 * Real.sqrt c ∧
    8 * C_pdef ^ 2 * (c ^ 7 / b_res) *
      (1 / Real.log (N : ℝ) + (1 + Real.log (R' : ℝ)) ^ 4 / (Real.log (N : ℝ)) ^ 2) ≤ 1 / 8 ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 ∧
    C_small * (c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / Real.log (N : ℝ) +
      ((1 + Real.log (R' : ℝ)) ^ 2 / Real.log (N : ℝ) +
        (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt (Real.log (N : ℝ))) +
      c * (1 + Real.log (R' : ℝ)) / Real.sqrt (Real.log (N : ℝ)) +
      c ^ 2 / Real.log (N : ℝ) +
      c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / Real.log (N : ℝ) +
      c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) +
      c ^ 5 * Real.log (N : ℝ) / (N : ℝ) +
      c ^ 4 / Real.sqrt (Q₁ : ℝ) +
      c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) +
      c ^ 2 * (1 + Real.log c) / Real.log (N : ℝ)) ≤ 1 := by
  let L := Real.log (N : ℝ)
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR'2 : 2 ≤ R' := hQ₁2.trans hQR'
  have hc_71 : c ≤ L ^ (2 / 71 : ℝ) :=
    hcα.trans (Real.rpow_le_rpow_of_exponent_le hL1 hα_71)
  have hcpow_α : ∀ k : ℕ, c ^ k ≤ L ^ ((k : ℝ) * α) := fun k => by
    have hp := pow_le_pow_left₀ hc0.le hcα k
    have he : (L ^ α) ^ k = L ^ ((k : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hcpow : ∀ k : ℕ, c ^ k ≤ L ^ ((2 * (k : ℝ)) / 71) := fun k => by
    have hp := pow_le_pow_left₀ hc0.le hc_71 k
    have he : (L ^ (2 / 71 : ℝ)) ^ k = L ^ ((2 * (k : ℝ)) / 71) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hcL : c ≤ L :=
    hc_71.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (2 / 71 : ℝ) ≤ 1))
  have hQ0 : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
  have h1Q_le : 1 + Real.log (Q₁ : ℝ) ≤ L ^ (6 / 25 : ℝ) :=
    (by linarith only [Real.log_le_sub_one_of_pos hQ0] : 1 + Real.log (Q₁ : ℝ) ≤ Q₁).trans
      (hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 hqmax))
  have h1R_le : 1 + Real.log (R' : ℝ) ≤ L ^ (37 / 80 : ℝ) := by
    have hc16 : c ^ 16 ≤ L ^ (23 / 50 : ℝ) :=
      (hcpow 16).trans (Real.rpow_le_rpow_of_exponent_le hL1
        (by norm_num : (2 * (16 : ℝ)) / 71 ≤ 23 / 50))
    have hlogQ : Real.log (Q₁ : ℝ) ≤ L ^ (23 / 50 : ℝ) :=
      ((Real.log_le_sub_one_of_pos hQ0).trans (by linarith only)).trans
        (hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1
          (by linarith only [hqmax] : q ≤ 23 / 50)))
    have h1_50 : 1 ≤ L ^ (23 / 50 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hlin : 1 + Real.log (R' : ℝ) ≤ (C_R + 2) * L ^ (23 / 50 : ℝ) := by
      have hCRc : C_R * c ^ 16 ≤ C_R * L ^ (23 / 50 : ℝ) :=
        mul_le_mul_of_nonneg_left hc16 hCR0.le
      linarith only [hR'_log, hCRc, hlogQ, h1_50]
    have hmul : L ^ (1 / 400 : ℝ) * L ^ (23 / 50 : ℝ) = L ^ (37 / 80 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    exact hlin.trans ((mul_le_mul_of_nonneg_right hCR_L (by positivity)).trans_eq hmul)
  have hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ L := by
    have hmul : L ^ (43 / 80 : ℝ) * L ^ (37 / 80 : ℝ) = L := by
      rw [← Real.rpow_add hL0, show (43 / 80 : ℝ) + 37 / 80 = 1 by norm_num, Real.rpow_one]
    calc
      36 * (1 + Real.log (R' : ℝ)) ≤ 36 * L ^ (37 / 80 : ℝ) :=
        mul_le_mul_of_nonneg_left h1R_le (by norm_num)
      _ ≤ L ^ (43 / 80 : ℝ) * L ^ (37 / 80 : ℝ) :=
        mul_le_mul_of_nonneg_right hL43 (by positivity)
      _ = L := hmul
  have hlog18 : 18 * (1 + Real.log (R' : ℝ)) ≤ L := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  obtain ⟨_, _, _, _, hR6N, hRNT_lin, hRNT_up, hR_sqrtL, hc5_N, hc3R4_N⟩ :=
    rpow_horizon_N_bounds_local hN1 hR'2 hc1 hH0 hL2000 hHL hLX hcL hlog36
  have h1L_le1 : 1 / L ≤ 1 := div_le_one_of_le₀ hL1 hL0.le
  have hR_sqrt1 : (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 1 := hR_sqrtL.trans h1L_le1
  let δ := L ^ (-ν)
  have hδ0 : 0 ≤ δ := by dsimp only [δ]; positivity
  have hmul_ν : L ^ ν * δ = 1 := by
    dsimp only [δ]
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hsqrtL : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
  have h1lc : 1 + Real.log c ≤ 2 * c := by
    have := Real.log_le_sub_one_of_pos hc0; linarith only [this, hc1]
  have h1R0 : 0 ≤ 1 + Real.log (R' : ℝ) := by
    have := Real.log_natCast_nonneg R'; positivity
  have hdiv1_le1 : (1 + Real.log (R' : ℝ)) / Real.sqrt L ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.mpr hL0)).mpr
    rw [hsqrtL]
    exact h1R_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hc71_div : c ^ 71 / L ^ 2 ≤ δ := by
    have hL2 : L ^ (2 : ℕ) = L ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
    calc
      c ^ 71 / L ^ 2 ≤ L ^ ((71 : ℝ) * α) / L ^ (2 : ℝ) := by
        rw [← hL2]; exact div_le_div_of_nonneg_right (hcpow_α 71) (by positivity)
      _ = L ^ (71 * α - 2) := by rw [← Real.rpow_sub hL0]; congr 1; ring
      _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [h71_gap, hν])
  have hbig1 : 64 * C_R ^ 5 ≤ L ^ ν := by
    have hp1 : 0 ≤ 64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17) := by positivity
    linarith only [hbig_ν, hp1, hCsmall0]
  have hbig2 : 64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17) ≤ L ^ ν := by
    have hp1 : 0 ≤ 64 * C_R ^ 5 := by positivity
    linarith only [hbig_ν, hp1, hCsmall0]
  have hbig3 : 64 ≤ L ^ ν := by
    have hp1 : 0 ≤ 64 * C_R ^ 5 := by positivity
    have hp2 : 0 ≤ 64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17) := by positivity
    linarith only [hbig_ν, hp1, hp2, hCsmall0]
  have hbig4 : 20 * C_small ≤ L ^ ν := by
    have hp1 : 0 ≤ 64 * C_R ^ 5 := by positivity
    have hp2 : 0 ≤ 64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17) := by positivity
    linarith only [hbig_ν, hp1, hp2]
  -- 1. `(1 + log R')^2.5 / L ≤ c^4 * √c`
  have hdiv25 : (1 + Real.log (R' : ℝ)) ^ 2 * Real.sqrt (1 + Real.log (R' : ℝ)) / L ≤
      c ^ 4 * Real.sqrt c := by
    have hlin : 1 + Real.log (R' : ℝ) ≤ C_R * c ^ 16 + L ^ (6 / 25 : ℝ) := by
      linarith only [hR'_log, h1Q_le]
    have hp5 := (pow_le_pow_left₀ h1R0 hlin 5).trans
      (add_pow_five_le (by positivity : 0 ≤ C_R * c ^ 16) (by positivity : 0 ≤ L ^ (6 / 25 : ℝ)))
    have hL65 : (L ^ (6 / 25 : ℝ)) ^ (5 : ℕ) = L ^ (6 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hterm1 : 32 * (C_R * c ^ 16) ^ 5 / L ^ 2 ≤ (1 / 2 : ℝ) * c ^ 9 := by
      calc
        32 * (C_R * c ^ 16) ^ 5 / L ^ 2 =
            (1 / 2 : ℝ) * c ^ 9 * ((64 * C_R ^ 5) * (c ^ 71 / L ^ 2)) := by ring
        _ ≤ (1 / 2 : ℝ) * c ^ 9 * (L ^ ν * δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hbig1 hc71_div (by positivity) (by positivity))
            (by positivity)
        _ = (1 / 2 : ℝ) * c ^ 9 := by rw [hmul_ν, mul_one]
    have hterm2 : 32 * (L ^ (6 / 25 : ℝ)) ^ 5 / L ^ 2 ≤ (1 / 2 : ℝ) * c ^ 9 := by
      rw [hL65]
      have hdivL : L ^ (6 / 5 : ℝ) / L ^ 2 ≤ δ := by
        have hL2 : L ^ (2 : ℕ) = L ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
        rw [hL2, ← Real.rpow_sub hL0]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
      have hc9 : 1 ≤ c ^ 9 := one_le_pow₀ hc1
      calc
        32 * L ^ (6 / 5 : ℝ) / L ^ 2 = (1 / 2 : ℝ) * (64 * (L ^ (6 / 5 : ℝ) / L ^ 2)) := by ring
        _ ≤ (1 / 2 : ℝ) * (L ^ ν * δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hbig3 hdivL (by positivity) (by positivity))
            (by norm_num)
        _ = 1 / 2 := by rw [hmul_ν, mul_one]
        _ ≤ (1 / 2 : ℝ) * c ^ 9 := by linarith only [hc9]
    have hsq_le : ((1 + Real.log (R' : ℝ)) ^ 2 * Real.sqrt (1 + Real.log (R' : ℝ)) / L) ^ 2 ≤
        (c ^ 4 * Real.sqrt c) ^ 2 := by
      have hlhs : ((1 + Real.log (R' : ℝ)) ^ 2 * Real.sqrt (1 + Real.log (R' : ℝ)) / L) ^ 2 =
          (1 + Real.log (R' : ℝ)) ^ 5 / L ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt h1R0]; ring
      have hrhs : (c ^ 4 * Real.sqrt c) ^ 2 = c ^ 9 := by
        rw [mul_pow, Real.sq_sqrt hc0.le]; ring
      rw [hlhs, hrhs]
      have hdiv5 := div_le_div_of_nonneg_right hp5 (sq_nonneg L)
      rw [add_div] at hdiv5
      linarith only [hdiv5, hterm1, hterm2]
    have hlhs0 : 0 ≤ (1 + Real.log (R' : ℝ)) ^ 2 * Real.sqrt (1 + Real.log (R' : ℝ)) / L := by
      positivity
    have hrhs0 : 0 ≤ c ^ 4 * Real.sqrt c := by positivity
    nlinarith only [hsq_le, hlhs0, hrhs0]
  -- 2. `hpdef_small`
  have hpdef_small : 8 * C_pdef ^ 2 * (c ^ 7 / b_res) *
      (1 / L + (1 + Real.log (R' : ℝ)) ^ 4 / L ^ 2) ≤ 1 / 8 := by
    have hlin : 1 + Real.log (R' : ℝ) ≤ C_R * c ^ 16 + L ^ (6 / 25 : ℝ) := by
      linarith only [hR'_log, h1Q_le]
    have hp4 := (pow_le_pow_left₀ h1R0 hlin 4).trans
      (add_pow_four_le (by positivity : 0 ≤ C_R * c ^ 16) (by positivity : 0 ≤ L ^ (6 / 25 : ℝ)))
    have hL24 : (L ^ (6 / 25 : ℝ)) ^ (4 : ℕ) = L ^ (24 / 25 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hc7_L : c ^ 7 / L ≤ δ := by
      calc
        c ^ 7 / L ≤ L ^ ((2 * (7 : ℝ)) / 71) / L :=
          div_le_div_of_nonneg_right (hcpow 7) hL0.le
        _ = L ^ ((2 * (7 : ℝ)) / 71 - 1) := by rw [Real.rpow_sub hL0, Real.rpow_one]
        _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    have hc7_L24 : c ^ 7 * L ^ (24 / 25 : ℝ) / L ^ 2 ≤ δ := by
      have hL2 : L ^ (2 : ℕ) = L ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
      calc
        c ^ 7 * L ^ (24 / 25 : ℝ) / L ^ 2 ≤
            L ^ ((2 * (7 : ℝ)) / 71) * L ^ (24 / 25 : ℝ) / L ^ (2 : ℝ) := by
          rw [← hL2]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcpow 7) (by positivity)) (by positivity)
        _ = L ^ ((2 * (7 : ℝ)) / 71 + 24 / 25 - 2) := by
          rw [Real.rpow_sub hL0, Real.rpow_add hL0]
        _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    have hinner : c ^ 7 * (1 / L + (1 + Real.log (R' : ℝ)) ^ 4 / L ^ 2) ≤
        (16 * C_R ^ 4 + 17) * δ := by
      have hdiv4 := div_le_div_of_nonneg_right hp4 (sq_nonneg L)
      rw [hL24] at hdiv4
      have hm := mul_le_mul_of_nonneg_left hdiv4 (pow_nonneg hc0.le 7)
      have heq : c ^ 7 * ((16 * (C_R * c ^ 16) ^ 4 + 16 * L ^ (24 / 25 : ℝ)) / L ^ 2) =
          16 * C_R ^ 4 * (c ^ 71 / L ^ 2) + 16 * (c ^ 7 * L ^ (24 / 25 : ℝ) / L ^ 2) := by ring
      rw [heq] at hm
      have ht2 : 16 * C_R ^ 4 * (c ^ 71 / L ^ 2) ≤ 16 * C_R ^ 4 * δ :=
        mul_le_mul_of_nonneg_left hc71_div (by positivity)
      have ht3 : 16 * (c ^ 7 * L ^ (24 / 25 : ℝ) / L ^ 2) ≤ 16 * δ :=
        mul_le_mul_of_nonneg_left hc7_L24 (by norm_num)
      have hsplit : c ^ 7 * (1 / L + (1 + Real.log (R' : ℝ)) ^ 4 / L ^ 2) =
          c ^ 7 / L + c ^ 7 * ((1 + Real.log (R' : ℝ)) ^ 4 / L ^ 2) := by ring
      linarith only [hsplit, hc7_L, hm, ht2, ht3]
    calc
      8 * C_pdef ^ 2 * (c ^ 7 / b_res) *
          (1 / L + (1 + Real.log (R' : ℝ)) ^ 4 / L ^ 2) =
        (8 * C_pdef ^ 2 / b_res) *
          (c ^ 7 * (1 / L + (1 + Real.log (R' : ℝ)) ^ 4 / L ^ 2)) := by ring
      _ ≤ (8 * C_pdef ^ 2 / b_res) * ((16 * C_R ^ 4 + 17) * δ) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (1 / 8 : ℝ) * ((64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17)) * δ) := by ring
      _ ≤ (1 / 8 : ℝ) * (L ^ ν * δ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbig2 hδ0) (by norm_num)
      _ = 1 / 8 := by rw [hmul_ν, mul_one]
  -- 3. Bound each of the 10 summands in `exists_high_band_coercivity_sharpened` by `2 * δ`
  have hL_div1 : ∀ a : ℝ, L ^ a / L = L ^ (a - 1) := fun a => by
    rw [Real.rpow_sub hL0, Real.rpow_one]
  have hL_mul_div1 : ∀ a b : ℝ, L ^ a * L ^ b / L = L ^ (a + b - 1) := fun a b => by
    rw [Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_one]
  have hL_mul_div : ∀ a b d : ℝ, L ^ a * L ^ b / L ^ d = L ^ (a + b - d) := fun a b d => by
    rw [Real.rpow_sub hL0, Real.rpow_add hL0]
  have h1L_δ : 1 / L ≤ δ := by
    rw [show 1 / L = L ^ (-1 : ℝ) by rw [one_div, ← Real.rpow_neg_one]]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
  have hs1 : c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L ≤ 2 * δ := by
    have hc2 := hcpow 2
    have h1 : c * (1 + Real.log c) ≤ 2 * c ^ 2 := by nlinarith only [hc0, h1lc]
    have hnum : c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) ≤
        2 * (L ^ ((2 * (2 : ℝ)) / 71) * L ^ (37 / 80 : ℝ)) := by
      calc
        c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) ≤ (2 * c ^ 2) * L ^ (37 / 80 : ℝ) :=
          mul_le_mul h1 h1R_le h1R0 (by positivity)
        _ ≤ 2 * (L ^ ((2 * (2 : ℝ)) / 71) * L ^ (37 / 80 : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hc2 (by positivity : 0 ≤ L ^ (37 / 80 : ℝ))
          linarith only [this]
    have hexp : L ^ ((2 * (2 : ℝ)) / 71 + 37 / 80 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L ≤
          (2 * (L ^ ((2 * (2 : ℝ)) / 71) * L ^ (37 / 80 : ℝ))) / L :=
        div_le_div_of_nonneg_right hnum hL0.le
      _ = 2 * (L ^ ((2 * (2 : ℝ)) / 71) * L ^ (37 / 80 : ℝ) / L) := by ring
      _ = 2 * L ^ ((2 * (2 : ℝ)) / 71 + 37 / 80 - 1) := by rw [hL_mul_div1]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hs2 : ((1 + Real.log (R' : ℝ)) ^ 2 / L +
      (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L) ≤ 2 * δ := by
    have hs2_R : (1 + Real.log (R' : ℝ)) ^ 2 / L ≤ δ := by
      have h1R_sq : (1 + Real.log (R' : ℝ)) ^ 2 ≤ L ^ (37 / 40 : ℝ) := by
        have hp := pow_le_pow_left₀ h1R0 h1R_le 2
        have he : (L ^ (37 / 80 : ℝ)) ^ (2 : ℕ) = L ^ (37 / 40 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
        exact hp.trans_eq he
      calc
        _ ≤ L ^ (37 / 40 : ℝ) / L := div_le_div_of_nonneg_right h1R_sq hL0.le
        _ = L ^ (37 / 40 - 1 : ℝ) := hL_div1 _
        _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    have hs2_Q : (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L ≤ δ := by
      have hQsq : (1 + Real.log (Q₁ : ℝ)) ^ 2 ≤ L ^ (12 / 25 : ℝ) := by
        have hp := pow_le_pow_left₀
          (by have := Real.log_natCast_nonneg Q₁; positivity) h1Q_le 2
        have he : (L ^ (6 / 25 : ℝ)) ^ (2 : ℕ) = L ^ (12 / 25 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
        exact hp.trans_eq he
      rw [hsqrtL]
      calc
        _ ≤ L ^ (12 / 25 : ℝ) / L ^ (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_right hQsq (by positivity)
        _ = L ^ (12 / 25 - 1 / 2 : ℝ) := by rw [← Real.rpow_sub hL0]
        _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    linarith only [hs2_R, hs2_Q]
  have hs3 : c * (1 + Real.log (R' : ℝ)) / Real.sqrt L ≤ 2 * δ := by
    have hexp : L ^ ((2 / 71 : ℝ) + 37 / 80 - 1 / 2) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    rw [hsqrtL]
    calc
      c * (1 + Real.log (R' : ℝ)) / L ^ (1 / 2 : ℝ) ≤
          L ^ (2 / 71 : ℝ) * L ^ (37 / 80 : ℝ) / L ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul hc_71 h1R_le h1R0 (by positivity)) (by positivity)
      _ = L ^ ((2 / 71 : ℝ) + 37 / 80 - 1 / 2) := hL_mul_div _ _ _
      _ ≤ δ := hexp
      _ ≤ 2 * δ := by linarith only [hδ0]
  have hs4 : c ^ 2 / L ≤ 2 * δ := by
    have hexp : L ^ ((2 * (2 : ℝ)) / 71 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c ^ 2 / L ≤ L ^ ((2 * (2 : ℝ)) / 71) / L :=
        div_le_div_of_nonneg_right (hcpow 2) hL0.le
      _ = L ^ ((2 * (2 : ℝ)) / 71 - 1) := hL_div1 _
      _ ≤ δ := hexp
      _ ≤ 2 * δ := by linarith only [hδ0]
  have hs5 : c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L ≤ 2 * δ := by
    have hc3 := hcpow 3
    have h1 : c ^ 2 * (1 + Real.log c) ≤ 2 * c ^ 3 := by nlinarith only [sq_nonneg c, hc0, h1lc]
    have hnum : c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) ≤
        2 * (L ^ ((2 * (3 : ℝ)) / 71) * L ^ (37 / 80 : ℝ)) := by
      calc
        c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) ≤ (2 * c ^ 3) * L ^ (37 / 80 : ℝ) :=
          mul_le_mul h1 h1R_le h1R0 (by positivity)
        _ ≤ 2 * (L ^ ((2 * (3 : ℝ)) / 71) * L ^ (37 / 80 : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ L ^ (37 / 80 : ℝ))
          linarith only [this]
    have hexp : L ^ ((2 * (3 : ℝ)) / 71 + 37 / 80 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L ≤
          (2 * (L ^ ((2 * (3 : ℝ)) / 71) * L ^ (37 / 80 : ℝ))) / L :=
        div_le_div_of_nonneg_right hnum hL0.le
      _ = 2 * (L ^ ((2 * (3 : ℝ)) / 71) * L ^ (37 / 80 : ℝ) / L) := by ring
      _ = 2 * L ^ ((2 * (3 : ℝ)) / 71 + 37 / 80 - 1) := by rw [hL_mul_div1]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hs6 : c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 2 * δ := by
    calc
      c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) =
          c ^ 2 * ((R' : ℝ) * Real.sqrt (L / (N : ℝ))) := by ring
      _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR_sqrtL (by positivity)
      _ = c ^ 2 / L := by ring
      _ ≤ 2 * δ := hs4
  have hs7 : c ^ 5 * L / (N : ℝ) ≤ 2 * δ := (hc5_N.trans h1L_δ).trans (by linarith only [hδ0])
  have hs8 : c ^ 4 / Real.sqrt (Q₁ : ℝ) ≤ 2 * δ := by
    have hsqrtQ : (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt (Q₁ : ℝ) := by
      have hsq : ((1 / 2 : ℝ) * L ^ (q / 2)) ^ 2 = (1 / 4 : ℝ) * L ^ q := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (q / 2)) 2, ← Real.rpow_mul hL0.le]; norm_num
      have hpos : 0 ≤ (1 / 2 : ℝ) * L ^ (q / 2) := by positivity
      exact (Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt (hsq.trans_le hQ_quarter))
    have hc4 := hcpow_α 4
    have hexp : L ^ ((4 : ℝ) * α - q / 2) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hsep])
    calc
      c ^ 4 / Real.sqrt (Q₁ : ℝ) ≤ L ^ ((4 : ℝ) * α) / ((1 / 2 : ℝ) * L ^ (q / 2)) :=
        (div_le_div_of_nonneg_right hc4 (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrtQ)
      _ = 2 * (L ^ ((4 : ℝ) * α) / L ^ (q / 2)) := by ring
      _ = 2 * L ^ ((4 : ℝ) * α - q / 2) := by rw [← Real.rpow_sub hL0]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hs9 : c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 2 * δ :=
    (hc3R4_N.trans h1L_δ).trans (by linarith only [hδ0])
  have hs10 : c ^ 2 * (1 + Real.log c) / L ≤ 2 * δ := by
    have hc3 := hcpow 3
    have h1 : c ^ 2 * (1 + Real.log c) ≤ 2 * c ^ 3 := by nlinarith only [sq_nonneg c, hc0, h1lc]
    have hexp : L ^ ((2 * (3 : ℝ)) / 71 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c ^ 2 * (1 + Real.log c) / L ≤ (2 * c ^ 3) / L := div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ (2 * L ^ ((2 * (3 : ℝ)) / 71)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 zero_le_two) hL0.le
      _ = 2 * (L ^ ((2 * (3 : ℝ)) / 71) / L) := by ring
      _ = 2 * L ^ ((2 * (3 : ℝ)) / 71 - 1) := by rw [hL_div1]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hsum_small : C_small * (c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L +
      ((1 + Real.log (R' : ℝ)) ^ 2 / L + (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L) +
      c * (1 + Real.log (R' : ℝ)) / Real.sqrt L +
      c ^ 2 / L +
      c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L +
      c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) +
      c ^ 5 * L / (N : ℝ) +
      c ^ 4 / Real.sqrt (Q₁ : ℝ) +
      c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) +
      c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have h10 : c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L +
        ((1 + Real.log (R' : ℝ)) ^ 2 / L + (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L) +
        c * (1 + Real.log (R' : ℝ)) / Real.sqrt L +
        c ^ 2 / L +
        c ^ 2 * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L +
        c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) +
        c ^ 5 * L / (N : ℝ) +
        c ^ 4 / Real.sqrt (Q₁ : ℝ) +
        c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) +
        c ^ 2 * (1 + Real.log c) / L ≤ 20 * δ := by
      linarith only [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10]
    calc
      _ ≤ C_small * (20 * δ) := mul_le_mul_of_nonneg_left h10 hCsmall0.le
      _ = (20 * C_small) * δ := by ring
      _ ≤ L ^ ν * δ := mul_le_mul_of_nonneg_right hbig4 hδ0
      _ = 1 := hmul_ν
  exact ⟨hcL, hlog36, hR6N, hlog18, hRNT_lin, hRNT_up, hdiv1_le1, hdiv25, hpdef_small,
    hR_sqrt1, hsum_small⟩

private theorem eventually_sharpened_low_band_and_coercivity_gap
    {K_res C_coerc α q ν : ℝ} {k : ℕ} (hK : 0 < K_res) (_hC_coerc : 0 < C_coerc)
    (_hα : 0 < α) (hα_lt : α < sharpenedPowerLogExponent)
    (hq : 0 < q) (hqmax : q ≤ 6 / 25) (hν : 0 < ν) (hk : 1 ≤ k)
    (hbudget_exp : 2 * q + 2 * ν + 19 * α + 1 / (k : ℝ) - 1 ≤ -ν)
    (hgap_pos : 0 < q / 4 - α) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ L ^ α →
        9 * (1 + Real.log (Q₁ : ℝ)) / L *
          (|completeWeilSelfFinitePart tiltedUnitSpline 1| +
            2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4) ≤ 1 / 16 ∧
        K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
          (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
            c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 128 ∧
        K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
          (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
            c ^ 3 * L ^ (1 / (k : ℝ)) / L) /
          (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) ^ 2 ≤ 1 / 36 ∧
        2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc ≤
          (1 / 4) * Real.log (Q₁ : ℝ) - Real.log c := by
  have hα_71 : α < 2 / 71 := hα_lt
  have hκ := tiltedSplineSpectralFloorConstant_pos
  let M_self := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  let M_rate := max 2 (max (384 * K_res) (432 * K_res / tiltedSplineSpectralFloorConstant ^ 2))
  let M_coerc := (2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc + 1 / 4) / (q / 4 - α)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_floor_log_rpow_bounds_sharpened hq hqmax,
    eventually_log_nat_le_rpow_36_local,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 25)).comp hLlim).eventually_ge_atTop
      (144 * M_self),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop M_rate,
    hLlim.eventually ((isLittleO_log_rpow_atTop hν).bound (by norm_num : (0 : ℝ) < 1 / 2)),
    hllim.eventually_ge_atTop M_coerc,
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 2] with
    N hQ_all hLX hL13 hLν hlogL_o hll hL1 hN2
  dsimp only [Function.comp_def] at hL13 hLν hll
  obtain ⟨hQ2, hQ_le, _, hlogQ_lb, _⟩ := hQ_all
  dsimp only
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  intro c hc1 hcup
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc_71 : c ≤ L ^ (2 / 71 : ℝ) :=
    hcup.trans (Real.rpow_le_rpow_of_exponent_le hL1 hα_71.le)
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  -- 1. Gram error bound
  have hgram : 9 * (1 + Real.log (Q₁ : ℝ)) / L *
      (|completeWeilSelfFinitePart tiltedUnitSpline 1| +
        2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4) ≤ 1 / 16 := by
    have hQ2' : 2 ≤ Q₁ := hQ2
    have hQ0 : (0 : ℝ) < Q₁ := Nat.cast_pos.mpr (zero_lt_two.trans_le hQ2')
    have hQ_625 : (Q₁ : ℝ) ≤ L ^ (6 / 25 : ℝ) :=
      hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 hqmax)
    have h1logQ : 1 + Real.log (Q₁ : ℝ) ≤ L ^ (6 / 25 : ℝ) :=
      (by linarith only [Real.log_le_sub_one_of_pos hQ0] : 1 + Real.log (Q₁ : ℝ) ≤ Q₁).trans hQ_625
    have hlogQ_625 : Real.log (Q₁ : ℝ) ≤ L ^ (6 / 25 : ℝ) := by linarith only [h1logQ]
    have hc4_625 : c ^ 4 ≤ L ^ (6 / 25 : ℝ) :=
      (hcpow 4).trans (Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith only [hα_71] : (4 : ℝ) * α ≤ 6 / 25))
    have h1_625 : 1 ≤ L ^ (6 / 25 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hbrack : |completeWeilSelfFinitePart tiltedUnitSpline 1| +
        2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4 ≤ M_self * L ^ (6 / 25 : ℝ) := by
      have ha : |completeWeilSelfFinitePart tiltedUnitSpline 1| ≤
          |completeWeilSelfFinitePart tiltedUnitSpline 1| * L ^ (6 / 25 : ℝ) := by
        nlinarith only [abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1), h1_625]
      dsimp only [M_self]
      linarith only [ha, hlogQ_625, hc4_625]
    have hexp : L ^ (6 / 25 : ℝ) * L ^ (6 / 25 : ℝ) / L = L ^ (-13 / 25 : ℝ) := by
      rw [show (-13 / 25 : ℝ) = 6 / 25 + 6 / 25 - 1 by norm_num,
        Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_one]
    have hmul1 : L ^ (13 / 25 : ℝ) * L ^ (-13 / 25 : ℝ) = 1 := by
      rw [← Real.rpow_add hL0, show (13 / 25 : ℝ) + (-13 / 25) = 0 by norm_num, Real.rpow_zero]
    calc
      9 * (1 + Real.log (Q₁ : ℝ)) / L *
          (|completeWeilSelfFinitePart tiltedUnitSpline 1| +
            2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4) ≤
          (9 * L ^ (6 / 25 : ℝ) / L) * (M_self * L ^ (6 / 25 : ℝ)) :=
        mul_le_mul (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1logQ (by norm_num)) hL0.le)
          hbrack (by have := Real.log_natCast_nonneg Q₁; positivity) (by positivity)
      _ = (9 * M_self) * (L ^ (6 / 25 : ℝ) * L ^ (6 / 25 : ℝ) / L) := by ring
      _ = (1 / 16 : ℝ) * ((144 * M_self) * L ^ (-13 / 25 : ℝ)) := by rw [hexp]; ring
      _ ≤ (1 / 16 : ℝ) * (L ^ (13 / 25 : ℝ) * L ^ (-13 / 25 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL13 (by positivity)) (by norm_num)
      _ = 1 / 16 := by rw [hmul1, mul_one]
  -- 2 & 3. Summed linear residual bounds (`Q₁^2 * (1 + log Q₁)^2`)
  have hsL : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hcL : c ≤ L := hc_71.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (2 / 71 : ℝ) ≤ 1))
  have hrate_le : c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
      c ^ 3 * L ^ (1 / (k : ℝ)) / L ≤ 3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L := by
    have hLN : c ^ 5 * (L / (N : ℝ)) ^ 2 ≤ 1 / L := by
      rw [div_pow, ← mul_div_assoc,
        div_le_div_iff₀ (sq_pos_of_pos hN0) hL0, one_mul]
      let X := (N : ℝ) ^ (1 / 36 : ℝ)
      have hX1 : 1 ≤ X := hL1.trans hLX
      have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
        dsimp only [X]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      have hL8 : L ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hL0.le hLX 8
      have hX8 : X ^ 8 ≤ (N : ℝ) :=
        (pow_le_pow_right₀ hX1 (by norm_num : 8 ≤ 36)).trans_eq hX36
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      calc
        c ^ 5 * L ^ 2 * L = c ^ 5 * L ^ 3 := by ring
        _ ≤ L ^ 5 * L ^ 3 := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hc0.le hcL 5) (by positivity)
        _ = L ^ 8 := by ring
        _ ≤ (N : ℝ) := hL8.trans hX8
        _ ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1R]
    have ht1 : c ^ 5 / L ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L :=
      div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hsL) hL0.le
    have ht2 : c ^ 10 * (L / (N : ℝ)) ^ 2 ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L := by
      calc
        _ = c ^ 5 * (c ^ 5 * (L / (N : ℝ)) ^ 2) := by ring
        _ ≤ c ^ 5 * (1 / L) := mul_le_mul_of_nonneg_left hLN (by positivity)
        _ = c ^ 5 / L := by ring
        _ ≤ _ := ht1
    have ht3 : c ^ 3 * L ^ (1 / (k : ℝ)) / L ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)) (by positivity)) hL0.le
    calc
      _ ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L + c ^ 5 * L ^ (1 / (k : ℝ)) / L +
          c ^ 5 * L ^ (1 / (k : ℝ)) / L := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L := by ring
  have hQ2_rpow : (Q₁ : ℝ) ^ 2 ≤ L ^ (2 * q) := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 2
    have he : (L ^ q) ^ (2 : ℕ) = L ^ (2 * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have h1logQ_sq : (1 + Real.log (Q₁ : ℝ)) ^ 2 ≤ L ^ (2 * ν) := by
    have hQ0 : (0 : ℝ) < Q₁ := Nat.cast_pos.mpr (zero_lt_two.trans_le hQ2)
    have hQ_L : (Q₁ : ℝ) ≤ L := hQ_le.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hqmax] : q ≤ 1))
    have hlogQ_L : Real.log (Q₁ : ℝ) ≤ Real.log L := Real.log_le_log hQ0 hQ_L
    have hlogL_half : Real.log L ≤ (1 / 2 : ℝ) * L ^ ν := by
      have habs : |Real.log L| ≤ (1 / 2 : ℝ) * L ^ ν := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0.le ν)] using hlogL_o
      exact (le_abs_self _).trans habs
    have h2_Lν : 2 ≤ L ^ ν := (le_max_left _ _).trans hLν
    have h1Q_Lν : 1 + Real.log (Q₁ : ℝ) ≤ L ^ ν := by
      linarith only [hlogQ_L, hlogL_half, h2_Lν]
    have hp := pow_le_pow_left₀
      (by have := Real.log_natCast_nonneg Q₁; positivity) h1Q_Lν 2
    have he : (L ^ ν) ^ (2 : ℕ) = L ^ (2 * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hQ2_c19 : ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
      c ^ 19 * L ^ (1 / (k : ℝ)) / L ≤ L ^ (-ν) := by
    calc
      _ ≤ (L ^ (2 * q) * L ^ (2 * ν)) * L ^ ((19 : ℝ) * α) * L ^ (1 / (k : ℝ)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul hQ2_rpow h1logQ_sq (sq_nonneg _) (by positivity))
            (hcpow 19) (by positivity) (by positivity))
          (by positivity)) hL0.le
      _ = L ^ (2 * q + 2 * ν + (19 : ℝ) * α + 1 / (k : ℝ) - 1) := by
        rw [Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0,
          Real.rpow_one]
      _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 hbudget_exp
  have hQ2_c5 : ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
      c ^ 5 * L ^ (1 / (k : ℝ)) / L ≤ L ^ (-ν) := by
    apply le_trans ?_ hQ2_c19
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by norm_num : 5 ≤ 19))
        (by positivity)) (by positivity)) hL0.le
  have hres_sum : K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
      (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
        c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 128 := by
    have hM1 : 384 * K_res ≤ L ^ ν :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hLν
    calc
      _ ≤ K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
            (3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L) :=
        mul_le_mul_of_nonneg_left hrate_le (by positivity)
      _ = (1 / 128 : ℝ) * ((384 * K_res) *
            (((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
              c ^ 5 * L ^ (1 / (k : ℝ)) / L)) := by ring
      _ ≤ (1 / 128 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM1 hQ2_c5 (by positivity) (by positivity))
          (by norm_num)
      _ = 1 / 128 := by rw [hmul_ν, mul_one]
  have hbudget : K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
      (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
        c ^ 3 * L ^ (1 / (k : ℝ)) / L) /
      (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) ^ 2 ≤ 1 / 36 := by
    have hM2 : 432 * K_res / tiltedSplineSpectralFloorConstant ^ 2 ≤ L ^ ν :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hLν
    calc
      _ ≤ K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
            (3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L) /
            (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrate_le (by positivity)) (sq_nonneg _)
      _ = (1 / 36 : ℝ) * ((432 * K_res / tiltedSplineSpectralFloorConstant ^ 2) *
            (((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) *
              c ^ 19 * L ^ (1 / (k : ℝ)) / L)) := by
        field_simp [hκ.ne', hc0.ne', hL0.ne']; ring
      _ ≤ (1 / 36 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM2 hQ2_c19 (by positivity) (by positivity))
          (by norm_num)
      _ = 1 / 36 := by rw [hmul_ν, mul_one]
  -- 4. Coercivity gap
  have hcoerc_gap : 2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc ≤
      (1 / 4) * Real.log (Q₁ : ℝ) - Real.log c := by
    have hlogc : Real.log c ≤ α * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 α)
    have hq_scaled : (q / 4) * Real.log L - 1 / 4 ≤ (1 / 4) * Real.log (Q₁ : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb (by norm_num : (0 : ℝ) ≤ 1 / 4)
      linarith only [hm]
    have hll_scaled : 2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc + 1 / 4 ≤
        (q / 4 - α) * Real.log L :=
      ((div_le_iff₀ hgap_pos).mp (show M_coerc ≤ Real.log L from hll)).trans_eq (mul_comm _ _)
    linarith only [hlogc, hq_scaled, hll_scaled]
  exact ⟨hgram, hres_sum, hbudget, hcoerc_gap⟩

/-- **Sharpened positive definiteness of `spectralFloorWeilMatrix c N` (`0 < α < 2 / 71`).** -/
theorem eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_sharpened
    {α : ℝ} (hα : 0 < α) (hα_lt : α < sharpenedPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (spectralFloorWeilMatrix c N).PosDef := by
  classical
  have hα_71_lt : α < 2 / 71 := hα_lt
  have hα_71 : α ≤ 2 / 71 := hα_71_lt.le
  let τ : ℝ := min ((2 - 71 * α) / 200) ((1 - 35 * α) / 200)
  have hτ : 0 < τ := lt_min (by linarith only [hα_71_lt]) (by linarith only [hα, hα_71_lt])
  have hτ1 : τ ≤ (2 - 71 * α) / 200 := min_le_left _ _
  have hτ2 : τ ≤ (1 - 35 * α) / 200 := min_le_right _ _
  let q : ℝ := 8 * α + τ
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqmax : q ≤ 6 / 25 := by dsimp only [q]; linarith only [hτ1, hα_71_lt, hα]
  let ν : ℝ := min (τ / 4) (1 / 1000)
  have hν : 0 < ν := lt_min (by positivity) (by norm_num)
  have hντ : ν ≤ τ / 4 := min_le_left _ _
  have hν1000 : ν ≤ 1 / 1000 := min_le_right _ _
  let k : ℕ := ⌈1 / τ⌉₊ + 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hrate : 1 / (k : ℝ) ≤ τ := by
    have hceil := Nat.le_ceil (1 / τ)
    have hτk : 1 ≤ τ * (k : ℝ) := by
      have h := (div_le_iff₀ hτ).mp hceil
      dsimp only [k]; push_cast; nlinarith only [h, hτ]
    exact (div_le_iff₀ hk0).mpr hτk
  have hsep : 4 * α - q / 2 ≤ -ν := by dsimp only [q]; linarith only [hντ, hτ]
  have h71_gap : 71 * α - 2 ≤ -4 * ν := by linarith only [hτ1, hντ, hτ]
  have hbudget_exp : 2 * q + 2 * ν + 19 * α + 1 / (k : ℝ) - 1 ≤ -ν := by
    dsimp only [q]
    linarith only [hτ2, hrate, hντ, hτ]
  have hgap : 0 < q / 4 - α := by dsimp only [q]; linarith only [hα, hτ]
  obtain ⟨C_R, C_pdef, H_res, b_res, hC_R, hC_pdef1, hH_res, hb_res, hsupp⟩ :=
    exists_high_tail_suppression_sharpened
  obtain ⟨C_coerc, C_small, hC_coerc, hC_small, hcoerc⟩ :=
    exists_high_band_coercivity_sharpened
  obtain ⟨K_res, hK_res, hres_lin⟩ :=
    exists_tiltedUnitSpline_linear_conductor_residual_variable_rate
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_floor_log_rpow_bounds_sharpened hq hqmax,
    eventually_log_nat_le_rpow_36_local,
    eventually_sharpened_low_band_and_coercivity_gap hK_res hC_coerc hα hα_lt
      hq hqmax hν hk hbudget_exp hgap,
    hres_lin q hq.le k hk,
    hLlim.eventually_ge_atTop (max 2000 H_res),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 43 / 80)).comp hLlim).eventually_ge_atTop 36,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 400)).comp hLlim).eventually_ge_atTop
      (C_R + 2),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop
      (64 * C_R ^ 5 + 64 * (C_pdef ^ 2 / b_res) * (16 * C_R ^ 4 + 17) +
        20 * C_small + 64),
    eventually_ge_atTop 2] with
    N hQ_all hLX hlow_coerc hresN hL_max hL43 hCR_L hbig_ν hN2
  dsimp only [Function.comp_def] at hL43 hCR_L hbig_ν
  obtain ⟨hQ2, hQ_le, hQ_quarter, _, hQ4_N⟩ := hQ_all
  have hL2000 : 2000 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hHL : H_res ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
  have hN1 : 1 ≤ N := by omega
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  intro c hc1 hcup
  obtain ⟨hgram, hres_sum_bound, hbudget, hcoerc_gap⟩ := hlow_coerc c hc1 hcup
  have hQ_R'_log : Real.log (Q₁ : ℝ) ≤ C_R * c ^ 16 + Real.log (Q₁ : ℝ) := by
    have : 0 ≤ C_R * c ^ 16 := by positivity
    linarith only [this]
  obtain ⟨hcL, hlog36_Q, _, hlog18_Q, _, _, _, _, _, _, _⟩ :=
    rpow_horizon_L_smallness_bounds_sharpened hα_71 h71_gap hqmax hν hν1000 hsep
      hN1 hQ2 le_rfl hc1 hC_R hC_pdef1 hb_res hC_small hH_res
      hL2000 hHL hLX hL43 hCR_L hbig_ν hQ_le hQ_quarter hcup hQ_R'_log
  obtain ⟨hHN, hwidth, hw1, hradN, _, _, _, _, _, _⟩ :=
    rpow_horizon_N_bounds_local hN1 hQ2 hc1 hH_res hL2000 hHL hLX hcL hlog36_Q
  have hQQ_N : Q₁ * Q₁ ≤ N := by
    have hQ2' : 2 ≤ Q₁ := hQ2
    have h24 : Q₁ ^ 2 ≤ Q₁ ^ 4 := Nat.pow_le_pow_right (zero_lt_two.trans_le hQ2') (by norm_num)
    simpa only [sq] using h24.trans hQ4_N
  let rate := c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 + c ^ 3 * L ^ (1 / (k : ℝ)) / L
  have hrate0 : 0 ≤ rate := by
    dsimp only [rate, L]; have := Real.log_natCast_nonneg N; positivity
  have hres_sum_raw :
      (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
        K_res * ((Q₁ : ℝ) ^ 2 * (1 + Real.log (Q₁ : ℝ)) ^ 2) * rate := by
    have hterm : ∀ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K_res * ((Q₁ : ℝ) * (1 + Real.log (Q₁ : ℝ)) ^ 2) * rate := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hmQ_R : (m : ℝ) ≤ Q₁ := by exact_mod_cast hmQ
      have hmL : (m : ℝ) ≤ L ^ q := hmQ_R.trans hQ_le
      have hlogm_le : 1 + Real.log (m : ℝ) ≤ 1 + Real.log (Q₁ : ℝ) := by
        have := Real.log_le_log (by exact_mod_cast hm1) hmQ_R
        linarith only [this]
      have hM_le : (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 2 ≤
          (Q₁ : ℝ) * (1 + Real.log (Q₁ : ℝ)) ^ 2 :=
        mul_le_mul hmQ_R
          (pow_le_pow_left₀ (by have := Real.log_natCast_nonneg m; positivity) hlogm_le 2)
          (sq_nonneg _) (Nat.cast_nonneg Q₁)
      exact (hresN m hm1 hmL c hc1 hwidth).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM_le hK_res.le) hrate0)
    have hsum := sum_le_sum hterm
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hsum
    exact hsum.trans_eq (by ring)
  have hres_sum_Q :
      (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 1 / 128 :=
    hres_sum_raw.trans hres_sum_bound
  apply matrix_posDef_of_sum_conductor_residuals
    (R := Q₁) (Q := Q₁)
    (e := tiltedSplineSpectralFloorConstant / (2 * c ^ 7))
    (spectralFloorWeilMatrix_isHermitian c N)
    (fun m => completedConductorEnergy tiltedUnitSpline c m -
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7))
    (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
    le_rfl hQ2 hQ4_N
    (fun m hm => spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1)
  · intro x hx hneg
    have hxE : completeWeilEnergy tiltedUnitSpline c N x ≤
        tiltedSplineSpectralFloorConstant / 2 := by
      rw [spectralFloorWeilMatrix_inner, hx, one_pow, mul_one] at hneg
      have hc7 : 1 ≤ c ^ 7 := one_le_pow₀ hc1
      have hfloor_le : tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
          tiltedSplineSpectralFloorConstant / 2 :=
        div_le_div_of_nonneg_left tiltedSplineSpectralFloorConstant_pos.le zero_lt_two
          (by linarith only [hc7])
      linarith only [hneg, hfloor_le]
    apply exists_raw_approx_of_starProjection_sq_le_local hN2 x
    by_contra hdist_not
    have hdist : 1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2 :=
      lt_of_not_ge hdist_not
    obtain ⟨zHat, hz_orth, hz_norm, hz_energy⟩ :=
      low_band_decoupling_unit_orthogonal_local hQ2 hQQ_N hlog18_Q hc1 hres_sum_Q hgram
        hx hxE hdist
    have hR'_conds : ∀ {R' : ℕ}, Q₁ ≤ R' →
        Real.log (R' : ℝ) ≤ C_R * c ^ 16 + Real.log (Q₁ : ℝ) →
        R' ^ 6 ≤ N ∧
        18 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ) ∧
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
        ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
        (1 + Real.log (R' : ℝ)) / Real.sqrt (Real.log (N : ℝ)) ≤ 1 ∧
        (1 + Real.log (R' : ℝ)) ^ 2 * Real.sqrt (1 + Real.log (R' : ℝ)) / Real.log (N : ℝ) ≤
          c ^ 4 * Real.sqrt c ∧
        8 * C_pdef ^ 2 * (c ^ 7 / b_res) *
          (1 / Real.log (N : ℝ) + (1 + Real.log (R' : ℝ)) ^ 4 / (Real.log (N : ℝ)) ^ 2) ≤ 1 / 8 ∧
        (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 := by
      intro R' hQR' hR'_log
      obtain ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ :=
        rpow_horizon_L_smallness_bounds_sharpened hα_71 h71_gap hqmax hν hν1000 hsep
          hN1 hQ2 hQR' hc1 hC_R hC_pdef1 hb_res hC_small hH_res
          hL2000 hHL hLX hL43 hCR_L hbig_ν hQ_le hQ_quarter hcup hR'_log
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    obtain ⟨R', hQR', hR'_log, u, hu_mem, hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩ :=
      hsupp hQ2 hc1 hHN hw1 hR'_conds hz_orth hz_norm hz_energy
    obtain ⟨_, hlog36_R', hR6N, _, hRNT_lin, _, _, _, _, _, hsum_small⟩ :=
      rpow_horizon_L_smallness_bounds_sharpened hα_71 h71_gap hqmax hν hν1000 hsep
        hN1 hQ2 hQR' hc1 hC_R hC_pdef1 hb_res hC_small hH_res
        hL2000 hHL hLX hL43 hCR_L hbig_ν hQ_le hQ_quarter hcup hR'_log
    have hlb := hcoerc hQ2 hQR' hR6N hlog36_R' hc1 hcL hw1 hradN hRNT_lin
      hsum_small hu_mem hu_orthQ hu_sq_ge hu_le1
    linarith only [hu_energy, hlb, hcoerc_gap]
  · have hsum_eq :
        (∑ m ∈ Icc 1 Q₁,
          ‖Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
              (normalizedRamanujanHorizonVector m N) -
            (completedConductorEnergy tiltedUnitSpline c m -
              tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) •
              normalizedRamanujanHorizonVector m N‖ ^ 2) =
        ∑ m ∈ Icc 1 Q₁,
          ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      sum_congr rfl fun m _ => by rw [spectralFloorWeilMatrix_residual_eq]
    rw [hsum_eq]
    exact (div_le_div_of_nonneg_right hres_sum_raw (sq_nonneg _)).trans hbudget

/-- **Sharpened uniform `c⁻⁷` spectral floor across `1 ≤ c ≤ (log N)^α` (`0 < α < 2 / 71`).** -/
theorem eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_sharpened
    {α : ℝ} (hα : 0 < α) (hα_lt : α < sharpenedPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
  filter_upwards [eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_sharpened hα hα_lt]
    with N hpos c hc hcup x
  have hA := spectralFloorWeilMatrix_isHermitian c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hnonneg : 0 ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [spectralFloorWeilMatrix_inner] at hnonneg
  linarith only [hnonneg]

/-- **Sharpened all-vector positivity of `completeWeilMatrix tiltedUnitSpline c N` (`0 < α < 2 / 71`).** -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_sharpened
    {α : ℝ} (hα : 0 < α) (hα_lt : α < sharpenedPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  classical
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_sharpened
    hα hα_lt] with N hfloor c hc hcup
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have hh : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh, norm_nonneg x]
  have heig_eq : completeWeilEnergy tiltedUnitSpline c N x = hA.eigenvalues i := by
    unfold completeWeilEnergy
    have hAx : Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x =
        hA.eigenvalues i • x := by
      ext j; exact congrFun (hA.mulVec_eigenvectorBasis i) j
    rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
  have hf := hfloor c hc hcup x
  rw [hx, one_pow, mul_one, heig_eq] at hf
  exact (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)).trans_le hf

/-- **Literal `weilQuad` nonnegativity across `1 ≤ c ≤ (log N)^α` (`0 < α < 2 / 71`).** -/
theorem eventually_tiltedUnitSpline_weilQuad_nonneg_sharpened
    {α : ℝ} (hα : 0 < α) (hα_lt : α < sharpenedPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ y : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef_sharpened hα hα_lt,
    eventually_ge_atTop 1] with N hpos hN c hc hcup y
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc0 hN0
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN] at hquad
  have htest : atomicTest N (primeHorizonExtension (horizonProfileVector y N))
      (atomDilate tiltedUnitSpline (c / N)) =
      atomicTest N y (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    exact congrArg (· * atomDilate tiltedUnitSpline (c / N) (u - Real.log n))
      (primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩)
  rw [htest, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hneg⟩
  · exact hq
  · linarith only [hM, hneg]

/-- **Sharpened zero-mass-loss `poleDefect` reserve (`0 < α < 2 / 71`).** -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_sharpened :
    ∃ b₁ : ℝ, 0 < b₁ ∧
      ∀ α : ℝ, 0 < α → α < sharpenedPowerLogExponent →
        ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
            (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) ≤
              completeWeilEnergy tiltedUnitSpline c N x ∧
            (b₁ / Real.log (N : ℝ)) * poleDefect N (primeHorizonExtension x) ≤
              completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hres⟩ := exists_matrix_polynomial_reserve_local
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  let b₁ := κ * b / (2 * B + κ)
  have hb₁ : 0 < b₁ := div_pos (mul_pos hκ hb) (by positivity)
  refine ⟨b₁, hb₁, ?_⟩
  intro α hα hα_lt
  have hα_71 : α < 2 / 71 := hα_lt
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_sharpened
      hα hα_lt,
    eventually_log_nat_le_rpow_36_local,
    hLlim.eventually_ge_atTop (max 1 H),
    eventually_ge_atTop 2] with N hfloor hLX hL_max hN2 c hc1 hcup x
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hHL : H ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hcL : c ≤ Real.log (N : ℝ) :=
    hcup.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα_71] : α ≤ 1))
  have hHN : H * c ^ 8 ≤ (N : ℝ) := by
    let X := (N : ℝ) ^ (1 / 36 : ℝ)
    have hX1 : 1 ≤ X := hL1.trans hLX
    have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
      dsimp only [X]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have hHX : H ≤ X := hHL.trans hLX
    have hc8 : c ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hc0.le (hcL.trans hLX) 8
    calc
      H * c ^ 8 ≤ X * X ^ 8 := mul_le_mul hHX hc8 (by positivity) (by positivity)
      _ = X ^ 9 := by ring
      _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 9 ≤ 36)).trans_eq hX36
  have hr := hres c hc1 N hHN x
  have hf := hfloor c hc1 hcup x
  change (κ / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N x at hf
  have hE0 : 0 ≤ completeWeilEnergy tiltedUnitSpline c N x :=
    (mul_nonneg (by positivity) (sq_nonneg ‖x‖)).trans hf
  have h1 := mul_le_mul_of_nonneg_left hr hκ.le
  have h2 := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * B * c ^ 16)
  have hcancel : (2 * B * c ^ 16) * ((κ / (2 * c ^ 7)) * ‖x‖ ^ 2) =
      κ * (B * c ^ 9 * ‖x‖ ^ 2) := by field_simp [hc0.ne']
  rw [hcancel] at h2
  have hcomb : κ * ((b / c ^ 7) * poleDefect N (primeHorizonExtension x)) ≤
      (2 * B * c ^ 16 + κ) * completeWeilEnergy tiltedUnitSpline c N x := by
    linarith only [h1, h2]
  have hc16 : 1 ≤ c ^ 16 := one_le_pow₀ hc1
  have hscale : (2 * B * c ^ 16 + κ) * completeWeilEnergy tiltedUnitSpline c N x ≤
      ((2 * B + κ) * c ^ 16) * completeWeilEnergy tiltedUnitSpline c N x :=
    mul_le_mul_of_nonneg_right (by nlinarith only [hκ, hc16]) hE0
  have hfirst : (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) ≤
      completeWeilEnergy tiltedUnitSpline c N x := by
    have hpos_d : 0 < (2 * B + κ) * c ^ 23 := by positivity
    rw [show (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) =
        (κ * b * poleDefect N (primeHorizonExtension x)) / ((2 * B + κ) * c ^ 23) by
      dsimp only [b₁]; rw [div_div, div_mul_eq_mul_div]]
    rw [div_le_iff₀ hpos_d]
    have hle := mul_le_mul_of_nonneg_right (hcomb.trans hscale) (pow_nonneg hc0.le 7)
    have h_lhs : κ * (b / c ^ 7 * poleDefect N (primeHorizonExtension x)) * c ^ 7 =
        κ * b * poleDefect N (primeHorizonExtension x) := by
      have hc7_ne : c ^ 7 ≠ 0 := pow_ne_zero 7 hc0.ne'
      calc
        κ * (b / c ^ 7 * poleDefect N (primeHorizonExtension x)) * c ^ 7 =
            (b / c ^ 7 * c ^ 7) * (κ * poleDefect N (primeHorizonExtension x)) := by ring
        _ = b * (κ * poleDefect N (primeHorizonExtension x)) := by rw [div_mul_cancel₀ _ hc7_ne]
        _ = κ * b * poleDefect N (primeHorizonExtension x) := by ring
    have h_rhs : (2 * B + κ) * c ^ 16 * completeWeilEnergy tiltedUnitSpline c N x * c ^ 7 =
        completeWeilEnergy tiltedUnitSpline c N x * ((2 * B + κ) * c ^ 23) := by ring
    rw [h_lhs, h_rhs] at hle
    exact hle
  have hc23_L : c ^ 23 ≤ Real.log (N : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hcup 23
    have he : (Real.log (N : ℝ) ^ α) ^ (23 : ℕ) = Real.log (N : ℝ) ^ (23 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    have h23 : 23 * α ≤ 1 := by linarith only [hα_71]
    exact (hp.trans_eq he).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 h23)
  have hsecond : (b₁ / Real.log (N : ℝ)) * poleDefect N (primeHorizonExtension x) ≤
      completeWeilEnergy tiltedUnitSpline c N x := by
    have hd0 := poleDefect_nonneg N (primeHorizonExtension x)
    exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hb₁.le (pow_pos hc0 23) hc23_L) hd0).trans hfirst
  exact ⟨hfirst, hsecond⟩

/-! ## Section 4: Polylogarithmic Confinement and Total Elimination of Nonpositive Conductors -/

/-- **Polylogarithmic confinement of any nonpositive conductor below `N^θ` (`0 < α < 1 / 4`).**
For every `0 < θ < 1 / 2`, `0 < α < 1 / 4`, and `A > 8 * α`, eventually in `N` and uniformly across
`1 ≤ c ≤ (log N)^α`, every conductor `m ∈ Icc 1 ⌊N^θ⌋₊` with nonpositive complete-Weil energy
must lie strictly below `(log N)^A`. -/
theorem eventually_tiltedUnitSpline_nonpositiveConductors_below_rpow_subset_polylog
    {θ α A : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hα0 : 0 < α) (hα : α < 1 / 4) (hA : 8 * α < A) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) ≤ 0 →
        (m : ℝ) < Real.log (N : ℝ) ^ A := by
  filter_upwards [
    CompletedArithmeticForms.eventually_tiltedUnitSpline_exceptionalConductors_above_polylog_empty
      hθ0 hθ hα0 hα hA,
    eventually_ge_atTop 2] with N hempty hN2 c hc1 hcup m hm hle
  by_contra hnot
  have hge : Real.log (N : ℝ) ^ A ≤ (m : ℝ) := le_of_not_gt hnot
  have hLA0 : 0 ≤ Real.log (N : ℝ) ^ A :=
    Real.rpow_nonneg (Real.log_natCast_nonneg N) A
  have hceil : ⌈Real.log (N : ℝ) ^ A⌉₊ ≤ m := Nat.ceil_le.mpr hge
  have hmem : m ∈ (Icc ⌈Real.log (N : ℝ) ^ A⌉₊ ⌊(N : ℝ) ^ θ⌋₊).filter (fun m =>
      completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) ≤ 0) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨hceil, (mem_Icc.mp hm).2⟩, hle⟩
  rw [hempty c hc1 hcup] at hmem
  exact absurd hmem (notMem_empty m)

private theorem one_div_log_le_norm_normalizedRamanujanHorizonVector_sq
    {m N : ℕ} (hN2 : 2 ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    1 / Real.log (N : ℝ) ≤ ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm0 : 0 < m := by omega
  have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [← sum_primeHorizonExtension_sq]
  have hsub : Ioc 0 m ⊆ Icc 1 N := fun n hn => by
    obtain ⟨hn0, hnm⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, hnm.trans hmN⟩
  have hterm : ∀ n ∈ Ioc 0 m,
      (Real.log (N : ℝ))⁻¹ * (normalizedRamanujanMode m n ^ 2 / (m : ℝ)) ≤
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 := by
    intro n hn
    obtain ⟨hn0, hnm⟩ := mem_Ioc.mp hn
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
    have hcoe : primeHorizonExtension (normalizedRamanujanHorizonVector m N) n =
        (Real.sqrt (Real.log (N : ℝ)))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n) := by
      rw [primeHorizonExtension_coe _ ⟨n, hsub hn⟩]; rfl
    rw [hcoe, mul_pow, inv_pow, Real.sq_sqrt hL0.le, div_pow, Real.sq_sqrt hn0R.le]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (sq_nonneg _) hn0R (by exact_mod_cast hnm))
      (inv_nonneg.mpr hL0.le)
  calc
    1 / Real.log (N : ℝ) =
        (Real.log (N : ℝ))⁻¹ * ((∑ n ∈ Ioc 0 (0 + m), normalizedRamanujanMode m n ^ 2) / (m : ℝ)) := by
      rw [CompletedArithmeticForms.sum_Ioc_normalizedRamanujanMode_sq hm0 0,
        div_self hm0R.ne', mul_one, one_div]
    _ = ∑ n ∈ Ioc 0 m, (Real.log (N : ℝ))⁻¹ * (normalizedRamanujanMode m n ^ 2 / (m : ℝ)) := by
      rw [zero_add, ← sum_div, mul_sum]
    _ ≤ ∑ n ∈ Ioc 0 m, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 :=
      sum_le_sum hterm
    _ ≤ ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- **Total elimination of nonpositive Ramanujan conductors across `1 ≤ m ≤ N` (`0 < α < 2 / 71`).**
Throughout `1 ≤ c ≤ (log N)^α` (`0 < α < sharpenedPowerLogExponent`), every Ramanujan horizon mode
`normalizedRamanujanHorizonVector m N` (`1 ≤ m ≤ N`) has strictly positive complete-Weil energy at
least `tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * log N)`, and the nonpositive conductor set
`{m ∈ Icc 1 N | completeWeilEnergy tiltedUnitSpline c N v_m ≤ 0}` is empty. -/
theorem eventually_tiltedUnitSpline_all_conductors_pos_sharpened
    {α : ℝ} (hα : 0 < α) (hα_lt : α < sharpenedPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (∀ m ∈ Icc 1 N,
        tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) ≤
          completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N)) ∧
      ((Icc 1 N).filter (fun m =>
        completeWeilEnergy tiltedUnitSpline c N
          (normalizedRamanujanHorizonVector m N) ≤ 0)) = ∅ := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_sharpened
      hα hα_lt,
    eventually_ge_atTop 2] with N hfloor hN2 c hc1 hcup
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpos_all : ∀ m ∈ Icc 1 N,
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) ≤
        completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
    have hnorm := one_div_log_le_norm_normalizedRamanujanHorizonVector_sq hN2 hm1 hmN
    have hf := hfloor c hc1 hcup (normalizedRamanujanHorizonVector m N)
    calc
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) =
          (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * (1 / Real.log (N : ℝ)) := by ring
      _ ≤ (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) *
            ‖normalizedRamanujanHorizonVector m N‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm
          (div_nonneg tiltedSplineSpectralFloorConstant_pos.le (by positivity))
      _ ≤ completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) := hf
  refine ⟨hpos_all, Finset.filter_eq_empty_iff.mpr fun m hm hle => ?_⟩
  have hlb := hpos_all m hm
  have hgt : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) :=
    div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
  linarith only [hlb, hle, hgt]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

end

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_global_negIndex_le_polynomialConductor
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.matrix_posDef_of_sum_conductor_residuals
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.fullWeilCenter_residual_linear_conductor_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_linear_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_linear_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sharpenedPowerLogExponent_pos
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.powerLogPositivityExponent_lt_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.one_div_36_lt_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_weilQuad_nonneg_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_sharpened
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_nonpositiveConductors_below_rpow_subset_polylog
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_all_conductors_pos_sharpened
