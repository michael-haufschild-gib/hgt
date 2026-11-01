import GaloisForLFunctions.ArithmeticDegenerationTheory.TheTiltedSplineHasARegularTail
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheCrossConductorPairings
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# The limiting mixed structure of the complete Weil family

In the conductor basis (normalized Ramanujan packets `r_e`) the complete Weil family of the tilted
spline degenerates: every entry `⟨W_{c,N} r_e, r_{e'}⟩` tends to `0` along every growing overlap
schedule. This file proves the finite-dimensional analogue of the nilpotent-orbit theorem: after
rescaling by the conductor-one decay `c⁷`, the family has a limit, the limit is diagonal in the
conductor basis, and its diagonal is the Jordan-totient form.

* **Limiting mixed structure** (`tendsto_rescaledConductorGram`): along every schedule `c_N → ∞`
  with `c_N ≤ (log N)^α`, `α < 1/8`,
  `c_N⁷ ⟨W_{c_N,N} r_e, r_{e'}⟩ → δ_{ee'} · J(e)`, `J(e) = (2A_φ/M) ζ(8) J₈(e)/φ(e) > 0`.
  The graded pieces are the conductors; the polarization on them is the Jordan coefficient; the
  extension data (cross pairings) vanish after rescaling.
* **Extension data** (`tendsto_rescaled_conductorDeviation`): the rescaled residual channels
  `c⁷(⟨W r_e, r_{e'}⟩ − E_e⟨r_e, r_{e'}⟩)` tend to `0`. The input is the relative cross-conductor
  bound `O((c⁸ (1 + log c)² (log N)^{1/k}/log N)²)` of HWV, which decays exactly below the exponent
  `1/8`.
* **Inheritance** (`eventually_pos_of_rescaled_limit`): on every fixed finite conductor packet the
  form is eventually positive definite along such schedules, inherited from the positive definite
  Jordan form.
* **Inheritance radius** (`inheritance_radius`): below the exponent `1/8` the rescaled extension
  data vanish on every fixed packet, while at every multiple of `(log N)^{1/8}` positivity of the
  conductor Gram over all conductors is RH (HWV). The polarization of the limit is inherited exactly
  up to the RH exponent; past it the extension data carry the zeros.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis HodgeTheoryWithoutVarieties

/-- The Jordan coefficient of the tilted spline, `J(m) = lim c⁷ E_m(c)`. -/
def jordanCoefficient (m : ℕ) : ℝ :=
  2 / (∫ u, tiltedUnitSpline u ^ 2) * tiltedTailConstant * zetaSum 8 * jordanTotient 8 m / m.totient

theorem jordanCoefficient_pos {m : ℕ} (hm : 0 < m) : 0 < jordanCoefficient m := by
  have := jordanTotient_eight_pos hm
  have := tiltedTailConstant_pos
  have := integral_tiltedUnitSpline_sq_pos
  have hz : 0 < zetaSum 8 := by
    have h1 := one_le_coprimeZetaSum (k := 8) (by norm_num) 1
    have hle : coprimeZetaSum 8 1 = zetaSum 8 := by simp [coprimeZetaSum, zetaSum]
    linarith
  have : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  unfold jordanCoefficient
  positivity

theorem tendsto_rpow_seven_mul_completedConductorEnergy_jordan (m : ℕ) :
    Tendsto (fun c => c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m) atTop
      (𝓝 (jordanCoefficient m)) :=
  tendsto_rpow_seven_mul_completedConductorEnergy_tiltedUnitSpline m

/-- The conductor Gram of the complete Weil family of the tilted spline. -/
def conductorEntry (c : ℝ) (N e e' : ℕ) : ℝ :=
  ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
    (normalizedRamanujanHorizonVector e N), normalizedRamanujanHorizonVector e' N⟫

/-- The residual channel (extension datum) of a conductor pair. -/
def conductorDeviation (c : ℝ) (N e e' : ℕ) : ℝ :=
  conductorEntry c N e e' - completedConductorEnergy tiltedUnitSpline c e *
    ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫

/-- The rescaled conductor Gram `c⁷ ⟨W_{c,N} r_e, r_{e'}⟩`. -/
def rescaledConductorGram (c : ℝ) (N e e' : ℕ) : ℝ := c ^ (7 : ℝ) * conductorEntry c N e e'

/-! ## Asymptotics of the error envelope -/

/-- For `α < 1/8` there is `k` with `L^{8α} (1 + log L)² L^{1/k}/L → 0`. -/
theorem exists_tendsto_envelope {α : ℝ} (hα : α < 1 / 8) :
    ∃ k : ℕ, 1 ≤ k ∧ Tendsto (fun L : ℝ => L ^ (8 * α) * (1 + Real.log L) ^ 2 *
      L ^ (1 / (k : ℝ)) / L) atTop (𝓝 0) := by
  set δ := 1 - 8 * α with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / δ)
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkδ : 1 / (k : ℝ) ≤ δ / 4 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]
    have := (div_lt_iff₀ hδ0).mp hk
    linarith
  refine ⟨k, hk1, ?_⟩
  have hlog := (isLittleO_log_rpow_atTop (r := δ / 4) (by positivity)).bound one_pos
  have hdec : Tendsto (fun L : ℝ => 4 * L ^ (-(δ / 4))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by positivity : 0 < δ / 4)).const_mul 4
  refine squeeze_zero' ?_ ?_ hdec
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : 0 < L := by linarith
    have : 0 ≤ 1 + Real.log L := by linarith [Real.log_nonneg hL]
    positivity
  · filter_upwards [eventually_ge_atTop 1, hlog] with L hL hlg
    have hL0 : 0 < L := by linarith
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    rw [Real.norm_of_nonneg hlogL, one_mul, Real.norm_of_nonneg (by positivity)] at hlg
    have h1 : 1 ≤ L ^ (δ / 4) := Real.one_le_rpow hL (by positivity)
    have hsq : (1 + Real.log L) ^ 2 ≤ 4 * L ^ (δ / 2) := by
      have : (1 + Real.log L) ≤ 2 * L ^ (δ / 4) := by linarith
      have h2 := pow_le_pow_left₀ (by linarith) this 2
      have h3 : (L ^ (δ / 4)) ^ 2 = L ^ (δ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num; ring_nf
      nlinarith [h3]
    have hexp : L ^ (8 * α) * L ^ (1 / (k : ℝ)) / L ≤ L ^ (-(3 * δ / 4)) := by
      rw [← Real.rpow_add hL0, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL (by rw [hδ] at hkδ ⊢; linarith)
    calc L ^ (8 * α) * (1 + Real.log L) ^ 2 * L ^ (1 / (k : ℝ)) / L
        = (1 + Real.log L) ^ 2 * (L ^ (8 * α) * L ^ (1 / (k : ℝ)) / L) := by ring
      _ ≤ (4 * L ^ (δ / 2)) * L ^ (-(3 * δ / 4)) := by
          gcongr
      _ = 4 * L ^ (-(δ / 4)) := by
          rw [mul_assoc, ← Real.rpow_add hL0]; congr 2; ring

theorem tendsto_log_cube_div_natCast :
    Tendsto (fun N : ℕ => Real.log N ^ 3 / (N : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  simpa using h

/-! ## The extension data vanish after rescaling -/

/-- **The rescaled extension data vanish** along every schedule `c_N → ∞`, `c_N ≤ (log N)^α`,
`α < 1/8`. -/
theorem tendsto_rescaled_conductorDeviation {α : ℝ} (hα : α < 1 / 8) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hcα : ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) {e e' : ℕ}
    (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N => c N ^ (7 : ℝ) * conductorDeviation (c N) N e e') atTop (𝓝 0) := by
  obtain ⟨K, hK, hdev⟩ := exists_relative_conductorDeviation_sum_le
  obtain ⟨k, hk1, henv⟩ := exists_tendsto_envelope hα
  set Q := max e e'
  set B := (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2
  have hB : 0 ≤ B := by
    have : 0 ≤ 1 + Real.log Q := by
      have : (1 : ℝ) ≤ Q := by exact_mod_cast le_max_of_le_left he
      linarith [Real.log_nonneg this]
    positivity
  have hdevN := hdev 1 zero_le_one k hk1
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the envelope `T_N = c⁸(1 + log c)² L^{1/k}/L + c¹² L/N`
  set T : ℕ → ℝ := fun N => c N ^ 7 * (c N * (1 + Real.log (c N)) ^ 2 *
      Real.log N ^ (1 / (k : ℝ)) / Real.log N + c N ^ 5 * Real.log N / (N : ℝ)) with hT
  have hT0 : Tendsto T atTop (𝓝 0) := by
    have h1 := henv.comp hL
    have h2 := tendsto_log_cube_div_natCast
    refine squeeze_zero' ?_ ?_ ((h1.add h2).trans (by simp))
    · filter_upwards [hc.eventually_ge_atTop 1] with N hN
      have : 0 ≤ 1 + Real.log (c N) := by linarith [Real.log_nonneg hN]
      have hN0 : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
      simp only [hT]
      positivity
    · filter_upwards [hc.eventually_ge_atTop 1, hcα, hL.eventually_ge_atTop 1] with N hN hNα hLN
      simp only [hT, Function.comp]
      set L := Real.log N
      have hL0 : 0 < L := by linarith
      have hcL : c N ≤ L := hNα.trans (by
        rcases le_or_gt α 1 with h | h
        · calc L ^ α ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLN h
            _ = L := Real.rpow_one L
        · linarith)
      have hlogc : 0 ≤ Real.log (c N) := Real.log_nonneg hN
      have hlogcL : Real.log (c N) ≤ Real.log L := Real.log_le_log (by linarith) hcL
      have hc8 : c N ^ 8 ≤ L ^ (8 * α) := by
        calc c N ^ 8 ≤ (L ^ α) ^ 8 := pow_le_pow_left₀ (by linarith) hNα 8
          _ = L ^ (8 * α) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
      have hc12 : c N ^ 12 ≤ L ^ 2 := by
        calc c N ^ 12 ≤ (L ^ α) ^ 12 := pow_le_pow_left₀ (by linarith) hNα 12
          _ = L ^ (12 * α) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
          _ ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLN (by linarith)
          _ = L ^ 2 := Real.rpow_two L
      have hNpos : (0 : ℝ) < N := by
        have : (1 : ℝ) ≤ L := hLN
        by_contra h
        push_neg at h
        have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
        simp [L, this] at hLN
      have hk0 : 0 ≤ L ^ (1 / (k : ℝ)) := by positivity
      have e1 : c N ^ 7 * (c N * (1 + Real.log (c N)) ^ 2 * L ^ (1 / (k : ℝ)) / L) =
          c N ^ 8 * (1 + Real.log (c N)) ^ 2 * L ^ (1 / (k : ℝ)) / L := by ring
      have e2 : c N ^ 7 * (c N ^ 5 * L / N) = c N ^ 12 * L / N := by ring
      rw [mul_add, e1, e2]
      gcongr
      · exact hc8
      · calc c N ^ 12 * L ≤ L ^ 2 * L := by gcongr
          _ = L ^ 3 := by ring
  -- extract the `(e, e')` entry from the relative sum
  have hJe := (tendsto_rpow_seven_mul_completedConductorEnergy_jordan e).comp hc
  have hJe' := (tendsto_rpow_seven_mul_completedConductorEnergy_jordan e').comp hc
  have hEpos : ∀ᶠ N : ℕ in atTop, 0 < c N ^ (7 : ℝ) *
      completedConductorEnergy tiltedUnitSpline (c N) e :=
    hJe.eventually (lt_mem_nhds (jordanCoefficient_pos he))
  have hEpos' : ∀ᶠ N : ℕ in atTop, 0 < c N ^ (7 : ℝ) *
      completedConductorEnergy tiltedUnitSpline (c N) e' :=
    hJe'.eventually (lt_mem_nhds (jordanCoefficient_pos he'))
  -- the dominating quantity
  set D : ℕ → ℝ := fun N => K * (1 + B) ^ 2 * T N ^ 2 *
      ((c N ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline (c N) e) *
        (c N ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline (c N) e'))
  have hD : Tendsto D atTop (𝓝 0) := by
    have := (((hT0.pow 2).const_mul (K * (1 + B) ^ 2)).mul (hJe.mul hJe'))
    simpa [D, mul_assoc] using this
  have hQlog : ∀ᶠ N : ℕ in atTop, (Q : ℝ) ≤ Real.log N ^ (1 : ℝ) := by
    simpa using hL.eventually_ge_atTop (Q : ℝ)
  have hsize : ∀ᶠ N : ℕ in atTop, 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ (N : ℝ) := by
    have hlo := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).bound
      (show (0 : ℝ) < 1 / (4 * (Real.exp 1 + 3) ^ 2) by positivity)
    filter_upwards [hc.eventually_ge_atTop 1, hcα, hL.eventually_ge_atTop 1, hlo] with
      N hN hNα hLN hlg
    have hL0 : 0 < Real.log N := by linarith
    simp only [Function.comp, id, Real.norm_of_nonneg hL0.le,
      Real.norm_of_nonneg (Nat.cast_nonneg N)] at hlg
    have hc2 : c N ^ 2 ≤ Real.log N := by
      calc c N ^ 2 ≤ (Real.log N ^ α) ^ 2 := pow_le_pow_left₀ (by linarith) hNα 2
        _ = Real.log N ^ (2 * α) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
        _ ≤ Real.log N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLN (by linarith)
        _ = Real.log N := Real.rpow_one _
    have hpos : (0 : ℝ) < 4 * (Real.exp 1 + 3) ^ 2 := by positivity
    calc 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ 4 * (Real.exp 1 + 3) ^ 2 * Real.log N := by gcongr
      _ ≤ 4 * (Real.exp 1 + 3) ^ 2 * (1 / (4 * (Real.exp 1 + 3) ^ 2) * N) := by gcongr
      _ = N := by field_simp
  refine squeeze_zero_norm' ?_ (by simpa using (Real.continuous_sqrt.tendsto 0).comp hD)
  filter_upwards [hdevN, hc.eventually_ge_atTop 1, hsize, hQlog, hEpos, hEpos'] with
    N hN hcN hsN hQN hpE hpE'
  have hsum := hN (c N) hcN hsN Q hQN
  set Ee := completedConductorEnergy tiltedUnitSpline (c N) e
  set Ee' := completedConductorEnergy tiltedUnitSpline (c N) e'
  have hc7 : 0 < c N ^ (7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hEe : 0 < Ee := pos_of_mul_pos_right hpE hc7.le
  have hEe' : 0 < Ee' := pos_of_mul_pos_right hpE' hc7.le
  -- the single term is bounded by the sum
  have hterm : conductorDeviation (c N) N e e' ^ 2 / (Ee * Ee') ≤
      K * (c N ^ 7 + B) ^ 2 * (c N * (1 + Real.log (c N)) ^ 2 * Real.log N ^ (1 / (k : ℝ)) /
        Real.log N + c N ^ 5 * Real.log N / (N : ℝ)) ^ 2 := by
    refine le_trans ?_ hsum
    have hmem : e ∈ Icc 1 Q := mem_Icc.mpr ⟨he, le_max_left _ _⟩
    have hmem' : e' ∈ Icc 1 Q := mem_Icc.mpr ⟨he', le_max_right _ _⟩
    have hnn : ∀ a ∈ Icc 1 Q, ∀ b ∈ Icc 1 Q, 0 ≤ (⟪Matrix.toEuclideanLin
        (completeWeilMatrix tiltedUnitSpline (c N) N) (normalizedRamanujanHorizonVector a N),
          normalizedRamanujanHorizonVector b N⟫ - completedConductorEnergy tiltedUnitSpline (c N) a *
          ⟪normalizedRamanujanHorizonVector a N, normalizedRamanujanHorizonVector b N⟫) ^ 2 /
        (completedConductorEnergy tiltedUnitSpline (c N) a *
          completedConductorEnergy tiltedUnitSpline (c N) b) := fun a ha b hb => by
      have := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
        (fun u hu => tiltedUnitSpline_eq_zero u hu) integral_tiltedUnitSpline_sq_pos
        (show (0 : ℝ) < c N by linarith) (mem_Icc.mp ha).1
      have := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
        (fun u hu => tiltedUnitSpline_eq_zero u hu) integral_tiltedUnitSpline_sq_pos
        (show (0 : ℝ) < c N by linarith) (mem_Icc.mp hb).1
      positivity
    calc conductorDeviation (c N) N e e' ^ 2 / (Ee * Ee')
        ≤ ∑ b ∈ Icc 1 Q, (⟪Matrix.toEuclideanLin
            (completeWeilMatrix tiltedUnitSpline (c N) N) (normalizedRamanujanHorizonVector e N),
              normalizedRamanujanHorizonVector b N⟫ -
              completedConductorEnergy tiltedUnitSpline (c N) e *
              ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector b N⟫) ^ 2 /
            (Ee * completedConductorEnergy tiltedUnitSpline (c N) b) :=
          single_le_sum (f := fun b => (⟪Matrix.toEuclideanLin
            (completeWeilMatrix tiltedUnitSpline (c N) N) (normalizedRamanujanHorizonVector e N),
              normalizedRamanujanHorizonVector b N⟫ -
              completedConductorEnergy tiltedUnitSpline (c N) e *
              ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector b N⟫) ^ 2 /
            (Ee * completedConductorEnergy tiltedUnitSpline (c N) b))
            (fun b hb => hnn e hmem b hb) hmem'
      _ ≤ _ := single_le_sum (f := fun a => ∑ b ∈ Icc 1 Q, (⟪Matrix.toEuclideanLin
            (completeWeilMatrix tiltedUnitSpline (c N) N) (normalizedRamanujanHorizonVector a N),
              normalizedRamanujanHorizonVector b N⟫ -
              completedConductorEnergy tiltedUnitSpline (c N) a *
              ⟪normalizedRamanujanHorizonVector a N, normalizedRamanujanHorizonVector b N⟫) ^ 2 /
            (completedConductorEnergy tiltedUnitSpline (c N) a *
              completedConductorEnergy tiltedUnitSpline (c N) b))
            (fun a ha => sum_nonneg fun b hb => hnn a ha b hb) hmem
  -- rescale
  have hB7 : (c N ^ 7 + B) ^ 2 ≤ (1 + B) ^ 2 * (c N ^ 7) ^ 2 := by
    have h1 : (1 : ℝ) ≤ c N ^ 7 := one_le_pow₀ hcN
    have : c N ^ 7 + B ≤ (1 + B) * c N ^ 7 := by nlinarith
    calc (c N ^ 7 + B) ^ 2 ≤ ((1 + B) * c N ^ 7) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ = (1 + B) ^ 2 * (c N ^ 7) ^ 2 := by ring
  have h7 : c N ^ (7 : ℝ) = c N ^ 7 := by norm_cast
  have hsq : (c N ^ (7 : ℝ) * conductorDeviation (c N) N e e') ^ 2 ≤ D N := by
    simp only [D, hT]
    rw [h7] at hpE hpE' ⊢
    have hd := (div_le_iff₀ (mul_pos hEe hEe')).mp hterm
    have hK0 := hK.le
    calc (c N ^ 7 * conductorDeviation (c N) N e e') ^ 2
        = (c N ^ 7) ^ 2 * conductorDeviation (c N) N e e' ^ 2 := by ring
      _ ≤ (c N ^ 7) ^ 2 * (K * (c N ^ 7 + B) ^ 2 * (c N * (1 + Real.log (c N)) ^ 2 *
            Real.log N ^ (1 / (k : ℝ)) / Real.log N + c N ^ 5 * Real.log N / (N : ℝ)) ^ 2 *
            (Ee * Ee')) := by gcongr
      _ ≤ (c N ^ 7) ^ 2 * (K * ((1 + B) ^ 2 * (c N ^ 7) ^ 2) * (c N * (1 + Real.log (c N)) ^ 2 *
            Real.log N ^ (1 / (k : ℝ)) / Real.log N + c N ^ 5 * Real.log N / (N : ℝ)) ^ 2 *
            (Ee * Ee')) := by gcongr
      _ = K * (1 + B) ^ 2 * (c N ^ 7 * (c N * (1 + Real.log (c N)) ^ 2 *
            Real.log N ^ (1 / (k : ℝ)) / Real.log N + c N ^ 5 * Real.log N / (N : ℝ))) ^ 2 *
            (c N ^ 7 * Ee * (c N ^ 7 * Ee')) := by ring
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-! ## The limit -/

/-- **The limiting mixed structure.** Along every schedule `c_N → ∞`, `c_N ≤ (log N)^α`, `α < 1/8`,
the rescaled conductor Gram converges to the Jordan-totient form:
`c_N⁷ ⟨W_{c_N,N} r_e, r_{e'}⟩ → δ_{ee'} J(e)`. -/
theorem tendsto_rescaledConductorGram {α : ℝ} (hα : α < 1 / 8) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hcα : ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) {e e' : ℕ}
    (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N => rescaledConductorGram (c N) N e e') atTop
      (𝓝 (if e = e' then jordanCoefficient e else 0)) := by
  have hdev := tendsto_rescaled_conductorDeviation hα hc hcα he he'
  have hJ := (tendsto_rpow_seven_mul_completedConductorEnergy_jordan e).comp hc
  have hG : Tendsto (fun N : ℕ => ⟪normalizedRamanujanHorizonVector e N,
      normalizedRamanujanHorizonVector e' N⟫) atTop (𝓝 (if e = e' then 1 else 0)) := by
    simp_rw [normalizedRamanujanHorizonVector_inner]
    exact tendsto_ramanujanPoleProfile_gram he he'
  have h := (hJ.mul hG).add hdev
  have hval : jordanCoefficient e * (if e = e' then 1 else 0) + 0 =
      if e = e' then jordanCoefficient e else 0 := by split_ifs <;> simp
  rw [hval] at h
  refine h.congr fun N => ?_
  simp only [Function.comp, rescaledConductorGram, conductorDeviation]
  ring

/-- The rescaled quadratic form of a fixed finite conductor packet converges to the Jordan form
`Σ J(e) b_e²`. -/
theorem tendsto_rescaled_packet {α : ℝ} (hα : α < 1 / 8) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hcα : ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) {S : Finset ℕ}
    (hS : ∀ e ∈ S, 0 < e) (b : ℕ → ℝ) :
    Tendsto (fun N => ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * rescaledConductorGram (c N) N e e') atTop
      (𝓝 (∑ e ∈ S, jordanCoefficient e * b e ^ 2)) := by
  have h : Tendsto (fun N => ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * rescaledConductorGram (c N) N e e')
      atTop (𝓝 (∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (if e = e' then jordanCoefficient e else 0))) :=
    tendsto_finsetSum _ fun e he => tendsto_finsetSum _ fun e' he' =>
      (tendsto_rescaledConductorGram hα hc hcα (hS e he) (hS e' he')).const_mul _
  refine h.trans (le_of_eq ?_)
  congr 1
  refine sum_congr rfl fun e he => ?_
  rw [sum_eq_single_of_mem e he (fun e' _ hne => by simp [Ne.symm hne])]
  simp only [if_true]
  ring

/-- **Inheritance on finite packets.** A nonzero fixed conductor packet is eventually strictly
positive along every schedule below the exponent `1/8`: the polarization of the Jordan form is
inherited. -/
theorem eventually_pos_of_rescaled_limit {α : ℝ} (hα : α < 1 / 8) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hcα : ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) {S : Finset ℕ}
    (hS : ∀ e ∈ S, 0 < e) {b : ℕ → ℝ} (hb : ∃ e ∈ S, b e ≠ 0) :
    ∀ᶠ N : ℕ in atTop, 0 < ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * conductorEntry (c N) N e e' := by
  have hpos : 0 < ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
    obtain ⟨e₀, he₀, hb₀⟩ := hb
    refine sum_pos' (fun e he => mul_nonneg (jordanCoefficient_pos (hS e he)).le (sq_nonneg _))
      ⟨e₀, he₀, mul_pos (jordanCoefficient_pos (hS e₀ he₀)) (pow_pos_of_ne_zero' hb₀)⟩
  filter_upwards [(tendsto_rescaled_packet hα hc hcα hS b).eventually (lt_mem_nhds hpos),
    hc.eventually_gt_atTop 0] with N hN hcN
  have hc7 : 0 < c N ^ (7 : ℝ) := Real.rpow_pos_of_pos hcN _
  have : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * rescaledConductorGram (c N) N e e' =
      c N ^ (7 : ℝ) * ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * conductorEntry (c N) N e e' := by
    rw [mul_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e' _ => ?_
    simp only [rescaledConductorGram]
    ring
  rw [this] at hN
  exact pos_of_mul_pos_right hN hc7.le

/-- **The inheritance radius is the RH exponent.** Below `1/8` the rescaled extension data of every
pair of conductors vanish along every schedule; at every multiple of `(log N)^{1/8}` positivity of
the conductor Gram over all conductors is equivalent to RH. -/
theorem inheritance_radius :
    (∀ α : ℝ, α < 1 / 8 → ∀ c : ℕ → ℝ, Tendsto c atTop atTop →
      (∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) → ∀ e e' : ℕ, 0 < e → 0 < e' →
        Tendsto (fun N => c N ^ (7 : ℝ) * conductorDeviation (c N) N e e') atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      0 ≤ ∑ e ∈ Icc 1 N, ∑ e' ∈ Icc 1 N, b e * b e' *
        conductorGram (completeWeilMatrix tiltedUnitSpline (2 * K * Real.log N ^ (1 / 8 : ℝ)) N)
          e e') :=
  ⟨fun _ hα _ hc hcα _ _ he he' => tendsto_rescaled_conductorDeviation hα hc hcα he he',
    riemannHypothesis_iff_conductorGram_nonneg_eighthRoot⟩

end GaloisForLFunctions.ArithmeticDegenerationTheory
