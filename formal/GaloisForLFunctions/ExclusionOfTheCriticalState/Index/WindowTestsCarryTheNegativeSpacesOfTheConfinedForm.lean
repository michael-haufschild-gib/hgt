import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesDecideTheCriticalRatio
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyGap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineVariationalCompactness
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoTerminalSupportGap
import GaloisForLFunctions.HTGeometry.TwoModeSquareCombination

/-!
# Window tests carry every negative space of the confined form

The confined form `Q_R` is lower semicontinuous along window tests converging in `L²` with bounded
confinement mass (`fullEnergy_le_of_tendsto_sq`): normalized, such a sequence has a subsequence with
an energy-domain limit of energy at most the limit energy (variational compactness), and the limit
is the `L²` limit. Window recovery (`exists_window_energy_recovery`) bounds the energies from above, so
every profile of the domain is the limit of window tests whose energies converge
(`exists_isWindowRecovery`).

* **Polarization** (`IsWindowRecovery.tendsto_mixedEnergy`). Lower semicontinuity at `Φ ± Ψ` and the
  parallelogram law `Q(X + Y) + Q(X - Y) = 2Q(X) + 2Q(Y)` force the energies of `H_n ± K_n` to
  converge, so the mixed energies of two recoveries converge.
* **Negative spaces** (`exists_window_family_of_negative`). If `Q_R ≤ -δ|t|²` on the span of
  profiles `Φ_0, …, Φ_{m-1}`, then window tests `H_i` have `Q_R ≤ -(δ/2)|t|²` on their span: the
  window Gram matrices converge entrywise to that of the `Φ_i`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ

local notation "Q" => criticalHalfLineFullEnergy

/-! ### Elementary closure properties -/

theorem integral_sq_add_le {f g : ℝ → ℝ} (hf2 : Integrable fun u => f u ^ 2)
    (hg2 : Integrable fun u => g u ^ 2) :
    (∫ u, (f u + g u) ^ 2) ≤ 2 * (∫ u, f u ^ 2) + 2 * ∫ u, g u ^ 2 := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf2.const_mul 2) (hg2.const_mul 2)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
    ((hf2.const_mul 2).add (hg2.const_mul 2)) (Eventually.of_forall fun u => ?_)
  show (f u + g u) ^ 2 ≤ 2 * f u ^ 2 + 2 * g u ^ 2
  nlinarith [sq_nonneg (f u - g u)]

theorem criticalHalfLineEnergyDomain_sub {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) : CriticalHalfLineEnergyDomain fun u => F u - G u := by
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hF.add_const_mul hG (-1)

theorem IsWindowTest.mono {A B : ℝ} {H : ℝ → ℝ} (h : IsWindowTest A H) (hAB : A ≤ B) :
    IsWindowTest B H :=
  ⟨h.contDiff, fun y hy => h.vanish y fun hy' => hy ⟨by linarith [hy'.1], hy'.2⟩⟩

theorem IsWindowTest.add_const_mul {A : ℝ} {H K : ℝ → ℝ} (hH : IsWindowTest A H)
    (hK : IsWindowTest A K) (c : ℝ) : IsWindowTest A fun u => H u + c * K u :=
  ⟨hH.contDiff.add (contDiff_const.mul hK.contDiff), fun y hy => by
    rw [hH.vanish y hy, hK.vanish y hy]; ring⟩

theorem IsWindowTest.finsetSum {ι : Type*} (s : Finset ι) {A : ℝ} {H : ι → ℝ → ℝ}
    (hH : ∀ i, IsWindowTest A (H i)) (c : ι → ℝ) : IsWindowTest A fun u => ∑ i ∈ s, c i * H i u :=
  ⟨ContDiff.sum fun i _ => contDiff_const.mul (hH i).contDiff, fun y hy => by
    simp [(hH _).vanish y hy]⟩

/-- **The confined energy of a finite combination** is its Gram form. -/
theorem fullEnergy_finsetSum_eq (R : ℝ) {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i, CriticalHalfLineEnergyDomain (F i)) (c : ι → ℝ) :
    Q R (fun u => ∑ i ∈ s, c i * F i u) =
      ∑ j ∈ s, ∑ k ∈ s, c j * c k * criticalHalfLineMixedEnergy R (F j) (F k) := by
  have hP : CriticalHalfLineEnergyDomain (fun u => ∑ i ∈ s, c i * F i u) :=
    criticalHalfLineEnergyDomain_finsetSum s hF c
  rw [← criticalHalfLineMixedEnergy_self R hP,
    criticalHalfLineMixedEnergy_finsetSum_left R s hF c hP]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [criticalHalfLineMixedEnergy_comm, criticalHalfLineMixedEnergy_finsetSum_left R s hF c (hF j),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [criticalHalfLineMixedEnergy_comm]
  ring

/-! ### Lower semicontinuity -/

/-- **Lower semicontinuity along smooth tests.** If smooth compactly supported profiles of the
domain converge in `L²` to `Y` with bounded confinement mass and their energies converge to `L`, then
`Q_R(Y) ≤ L`. -/
theorem fullEnergy_le_of_tendsto_sq {R : ℝ} (hR : 0 < R) {U : ℕ → ℝ → ℝ}
    (hU : ∀ n, CriticalHalfLineEnergyDomain (U n)) (hUd : ∀ n, ContDiff ℝ 2 (U n))
    (hUc : ∀ n, HasCompactSupport (U n)) {Y : ℝ → ℝ} (hY : CriticalHalfLineEnergyDomain Y)
    (hL2 : Tendsto (fun n => ∫ u, (U n u - Y u) ^ 2) atTop (𝓝 0)) {M : ℝ}
    (hW : ∀ n, (∫ u, U n u ^ 2 * Real.exp (-(8 * u))) ≤ M) {L : ℝ}
    (hE : Tendsto (fun n => Q R (U n)) atTop (𝓝 L)) : Q R Y ≤ L := by
  have hdiff : ∀ n, CriticalHalfLineEnergyDomain (fun u => U n u - Y u) := fun n =>
    criticalHalfLineEnergyDomain_sub (hU n) hY
  set m := ∫ u, Y u ^ 2 with hmdef
  have hm0 : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hmass : Tendsto (fun n => ∫ u, U n u ^ 2) atTop (𝓝 m) := by
    have h := HTGeometry.tendsto_integral_sq_add_of_tendsto_zero (l := atTop) (μ := volume)
      (f := fun _ => Y) (g := fun n u => U n u - Y u)
      (Eventually.of_forall fun _ => hY.meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdiff n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun _ => hY.sq) (Eventually.of_forall fun n => (hdiff n).sq)
      tendsto_const_nhds hL2
    refine h.congr fun n => integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (Y u + (U n u - Y u)) ^ 2 = U n u ^ 2
    ring
  set μ := criticalHalfLineGroundEnergy R
  have hlow : ∀ n, μ * (∫ u, U n u ^ 2) ≤ Q R (U n) := fun n =>
    criticalHalfLineGroundEnergy_mul_mass_le_all hR (hU n)
  have hZ : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) :=
    criticalHalfLineEnergyDomain_of_compact_negative contDiff_const HasCompactSupport.zero
      fun _ _ => rfl
  rcases hm0.eq_or_lt with hm | hm
  · have hY0 : Y =ᵐ[volume] fun _ => (0 : ℝ) := by
      have h := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (Y u)) hY.sq).mp hm.symm
      filter_upwards [h] with u hu
      simpa using hu
    have hQ0 : Q R Y = 0 := by
      rw [criticalHalfLineFullEnergy_congr_ae hY hZ hY0 R]
      have h := criticalHalfLineFullEnergy_const_mul R Y 0
      norm_num at h
      exact h
    rw [hQ0]
    have h := hmass.const_mul μ
    rw [← hm, mul_zero] at h
    exact le_of_tendsto_of_tendsto h hE (Eventually.of_forall hlow)
  · -- normalize the masses
    set mx : ℕ → ℝ := fun n => max (∫ u, U n u ^ 2) (m / 2) with hmx
    have hmxpos : ∀ n, 0 < mx n := fun n => lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hmxlim : Tendsto mx atTop (𝓝 m) := by
      have h := hmass.max (tendsto_const_nhds (x := m / 2))
      rwa [max_eq_left (by linarith)] at h
    set r : ℕ → ℝ := fun n => 1 / Real.sqrt (mx n) with hr
    have hr_sq : ∀ n, r n ^ 2 = 1 / mx n := fun n => by
      simp only [hr, div_pow, one_pow, Real.sq_sqrt (hmxpos n).le]
    have hrlim : Tendsto r atTop (𝓝 (1 / Real.sqrt m)) :=
      tendsto_const_nhds.div hmxlim.sqrt (Real.sqrt_pos.mpr hm).ne'
    have hr2lim : Tendsto (fun n => r n ^ 2) atTop (𝓝 (1 / m)) := by
      have h := hrlim.pow 2
      rwa [div_pow, one_pow, Real.sq_sqrt hm.le] at h
    set V : ℕ → ℝ → ℝ := fun n u => r n * U n u with hV
    have hVd : ∀ n, CriticalHalfLineEnergyDomain (V n) := fun n => (hU n).const_mul (r n)
    have hVmass : ∀ n, (∫ u, V n u ^ 2) = r n ^ 2 * ∫ u, U n u ^ 2 := fun n => by
      simp_rw [hV, mul_pow]
      exact integral_const_mul _ _
    have hVle : ∀ n, (∫ u, V n u ^ 2) ≤ 1 := fun n => by
      rw [hVmass, hr_sq, one_div_mul_eq_div]
      exact div_le_one_of_le₀ (le_max_left _ _) (hmxpos n).le
    have hVlim : Tendsto (fun n => ∫ u, V n u ^ 2) atTop (𝓝 1) := by
      have h := hr2lim.mul hmass
      rw [one_div_mul_cancel hm.ne'] at h
      exact h.congr fun n => (hVmass n).symm
    have hM0 : 0 ≤ M := le_trans (integral_nonneg fun u => by positivity) (hW 0)
    have hVW : ∀ n, (∫ u, V n u ^ 2 * Real.exp (-(8 * u))) ≤ 2 / m * M := fun n => by
      have e : (∫ u, V n u ^ 2 * Real.exp (-(8 * u))) =
          r n ^ 2 * ∫ u, U n u ^ 2 * Real.exp (-(8 * u)) := by
        simp_rw [hV, mul_pow, mul_assoc]
        exact integral_const_mul _ _
      rw [e, hr_sq]
      have h1 : 1 / mx n ≤ 2 / m := by
        rw [div_le_div_iff₀ (hmxpos n) hm]
        have := le_max_right (∫ u, U n u ^ 2) (m / 2)
        linarith
      exact mul_le_mul h1 (hW n) (integral_nonneg fun u => by positivity) (by positivity)
    have hVE : Tendsto (fun n => Q R (V n)) atTop (𝓝 (1 / m * L)) := by
      refine (hr2lim.mul hE).congr fun n => ?_
      simp only [hV]
      rw [criticalHalfLineFullEnergy_const_mul]
    obtain ⟨B, hB⟩ := hVE.bddAbove_range
    obtain ⟨F, s, hs, hF, -, hFE, -, hFL2, -⟩ := exists_domain_limit_of_smooth_energy_limit hR hVd
      (fun n => contDiff_const.mul (hUd n)) (fun n => (hUc n).mul_left) hVle hVlim
      (by positivity : (0 : ℝ) ≤ 2 / m * M) hVW (B := B) (fun n => hB ⟨n, rfl⟩) hVE
    -- the limit is the normalized `L²` limit
    set c : ℝ := 1 / Real.sqrt m with hc
    have hcY : CriticalHalfLineEnergyDomain (fun u => c * Y u) := hY.const_mul c
    have hVc : Tendsto (fun n => ∫ u, (V n u - c * Y u) ^ 2) atTop (𝓝 0) := by
      have hb : ∀ n, (∫ u, (V n u - c * Y u) ^ 2) ≤
          2 * (r n ^ 2 * ∫ u, (U n u - Y u) ^ 2) + 2 * ((r n - c) ^ 2 * m) := fun n => by
        have h := integral_sq_add_le (f := fun u => r n * (U n u - Y u))
          (g := fun u => (r n - c) * Y u) (by simpa only [mul_pow] using (hdiff n).sq.const_mul _)
          (by simpa only [mul_pow] using hY.sq.const_mul _)
        have e1 : (∫ u, (r n * (U n u - Y u)) ^ 2) = r n ^ 2 * ∫ u, (U n u - Y u) ^ 2 := by
          simp_rw [mul_pow]; exact integral_const_mul _ _
        have e2 : (∫ u, ((r n - c) * Y u) ^ 2) = (r n - c) ^ 2 * m := by
          simp_rw [mul_pow]; exact integral_const_mul _ _
        rw [e1, e2] at h
        refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun u => ?_)) h
        show (V n u - c * Y u) ^ 2 = (r n * (U n u - Y u) + (r n - c) * Y u) ^ 2
        simp only [hV]
        ring
      have hlim : Tendsto (fun n => 2 * (r n ^ 2 * ∫ u, (U n u - Y u) ^ 2) +
          2 * ((r n - c) ^ 2 * m)) atTop (𝓝 0) := by
        have h1 := (hr2lim.mul hL2).const_mul 2
        have h2 := (((hrlim.sub_const c).pow 2).mul_const m).const_mul 2
        rw [sub_self, mul_zero, mul_zero] at h1
        rw [← hc, sub_self] at h2
        norm_num at h2
        simpa using h1.add h2
      exact squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) hb hlim
    have hFY : (∫ u, (F u - c * Y u) ^ 2) = 0 := by
      have hb : ∀ n, (∫ u, (F u - c * Y u) ^ 2) ≤
          2 * (∫ u, (V (s n) u - F u) ^ 2) + 2 * ∫ u, (V (s n) u - c * Y u) ^ 2 := fun n => by
        have h := integral_sq_add_le (f := fun u => -(V (s n) u - F u))
          (g := fun u => V (s n) u - c * Y u)
          (by simpa only [neg_sq] using (criticalHalfLineEnergyDomain_sub (hVd (s n)) hF).sq)
          (criticalHalfLineEnergyDomain_sub (hVd (s n)) hcY).sq
        simp only [neg_sq] at h
        refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun u => ?_)) h
        show (F u - c * Y u) ^ 2 = (-(V (s n) u - F u) + (V (s n) u - c * Y u)) ^ 2
        ring
      have hlim : Tendsto (fun n => 2 * (∫ u, (V (s n) u - F u) ^ 2) +
          2 * ∫ u, (V (s n) u - c * Y u) ^ 2) atTop (𝓝 0) := by
        simpa using (hFL2.const_mul 2).add ((hVc.comp hs.tendsto_atTop).const_mul 2)
      exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb))
        (integral_nonneg fun u => sq_nonneg _)
    have hae : F =ᵐ[volume] fun u => c * Y u := by
      have h := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (F u - c * Y u))
        (criticalHalfLineEnergyDomain_sub hF hcY).sq).mp hFY
      filter_upwards [h] with u hu
      have : (F u - c * Y u) ^ 2 = 0 := hu
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    have hQ : Q R (fun u => c * Y u) ≤ 1 / m * L := by
      rw [← criticalHalfLineFullEnergy_congr_ae hF hcY hae R]
      exact hFE
    rw [criticalHalfLineFullEnergy_const_mul, hc, div_pow, one_pow, Real.sq_sqrt hm.le] at hQ
    have := mul_le_mul_of_nonneg_left hQ hm.le
    rwa [← mul_assoc, ← mul_assoc, mul_one_div_cancel hm.ne', one_mul, one_mul] at this

/-! ### Window recoveries -/

/-- A window recovery of `Φ` at ratio `R`: window tests converging to `Φ` in `L²` with bounded
confinement mass, whose energies converge to that of `Φ`. -/
structure IsWindowRecovery (R : ℝ) (Φ : ℝ → ℝ) (H : ℕ → ℝ → ℝ) : Prop where
  window : ∀ n, ∃ A, 0 ≤ A ∧ IsWindowTest A (H n)
  sq : Tendsto (fun n => ∫ u, (H n u - Φ u) ^ 2) atTop (𝓝 0)
  weight : ∃ M, ∀ n, (∫ u, H n u ^ 2 * Real.exp (-(8 * u))) ≤ M
  energy : Tendsto (fun n => Q R (H n)) atTop (𝓝 (Q R Φ))

theorem IsWindowRecovery.domain {R : ℝ} {Φ : ℝ → ℝ} {H : ℕ → ℝ → ℝ}
    (h : IsWindowRecovery R Φ H) (n : ℕ) : CriticalHalfLineEnergyDomain (H n) :=
  criticalHalfLineEnergyDomain_of_window (h.window n).choose_spec.2

/-- Bounded masses along an `L²`-convergent sequence. -/
theorem exists_mass_bound {H : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} (hH : ∀ n, CriticalHalfLineEnergyDomain (H n))
    (hΦ : CriticalHalfLineEnergyDomain Φ)
    (hL2 : Tendsto (fun n => ∫ u, (H n u - Φ u) ^ 2) atTop (𝓝 0)) :
    ∃ C, ∀ n, (∫ u, H n u ^ 2) ≤ C := by
  obtain ⟨D, hD⟩ := hL2.bddAbove_range
  refine ⟨2 * D + 2 * ∫ u, Φ u ^ 2, fun n => ?_⟩
  have h := integral_sq_add_le (criticalHalfLineEnergyDomain_sub (hH n) hΦ).sq hΦ.sq
  have hd := hD ⟨n, rfl⟩
  refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun u => ?_))) (h.trans
    (by linarith))
  show H n u ^ 2 = (H n u - Φ u + Φ u) ^ 2
  ring

/-- **Every profile of the domain has a window recovery.** -/
theorem exists_isWindowRecovery {R : ℝ} (hR : 0 < R) {Φ : ℝ → ℝ}
    (hΦ : CriticalHalfLineEnergyDomain Φ) (hm : (∫ u, Φ u ^ 2) ≤ 1) :
    ∃ H : ℕ → ℝ → ℝ, IsWindowRecovery R Φ H := by
  have h := fun n : ℕ => exists_window_energy_recovery hR hΦ hm (ε := 1 / ((n : ℝ) + 1))
    (by positivity)
  choose A H hA hHw hmH hdH hH8 heH using h
  have hD : ∀ n, CriticalHalfLineEnergyDomain (H n) := fun n =>
    criticalHalfLineEnergyDomain_of_window (hHw n)
  have hL2 : Tendsto (fun n => ∫ u, (H n u - Φ u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) (fun n => (hdH n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨H, ⟨fun n => ⟨A n, hA n, hHw n⟩, hL2, ⟨_, hH8⟩, ?_⟩⟩
  obtain ⟨C, hC⟩ := exists_mass_bound hD hΦ hL2
  set μ := criticalHalfLineGroundEnergy R
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hlow : ∀ n, -(|μ| * |C|) ≤ Q R (H (ns n)) := fun n => by
    have h1 := criticalHalfLineGroundEnergy_mul_mass_le_all hR (hD (ns n))
    have h2 := hC (ns n)
    have h3 : 0 ≤ ∫ u, H (ns n) u ^ 2 := integral_nonneg fun u => sq_nonneg _
    nlinarith [neg_abs_le μ, le_abs_self μ, le_abs_self C, abs_nonneg μ]
  have hup : ∀ n, Q R (H (ns n)) ≤ Q R Φ + 1 := fun n => by
    have := heH (ns n)
    have : 1 / ((ns n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ)
      (ns n)]) (by positivity)
    linarith
  obtain ⟨L', -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc
    (-(|μ| * |C|)) (Q R Φ + 1)) (x := fun n => Q R (H (ns n))) fun n => ⟨hlow n, hup n⟩
  have hsub : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hge : Q R Φ ≤ L' := fullEnergy_le_of_tendsto_sq hR (fun n => hD (ns (φ n)))
    (fun n => (hHw (ns (φ n))).contDiff) (fun n => (hHw (ns (φ n))).hasCompactSupport) hΦ
    (hL2.comp hsub) (fun n => hH8 (ns (φ n))) hlim
  have hle : L' ≤ Q R Φ := by
    have h1 : Tendsto (fun n => Q R Φ + 1 / ((ns (φ n) : ℝ) + 1)) atTop (𝓝 (Q R Φ + 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsub)
    rw [add_zero] at h1
    exact le_of_tendsto_of_tendsto hlim h1 (Eventually.of_forall fun n => (heH (ns (φ n))).le)
  exact ⟨φ, by rw [← le_antisymm hle hge]; exact hlim⟩

/-- Sums and differences of two window recoveries are smooth window profiles with bounded mass. -/
private theorem recovery_combination {R : ℝ} {Φ Ψ : ℝ → ℝ} {H K : ℕ → ℝ → ℝ}
    (hH : IsWindowRecovery R Φ H) (hK : IsWindowRecovery R Ψ K) (hΦ : CriticalHalfLineEnergyDomain Φ)
    (hΨ : CriticalHalfLineEnergyDomain Ψ) (c : ℝ) (hc : c ^ 2 = 1) :
    (∀ n, CriticalHalfLineEnergyDomain fun u => H n u + c * K n u) ∧
    (∀ n, ContDiff ℝ 2 fun u => H n u + c * K n u) ∧
    (∀ n, HasCompactSupport fun u => H n u + c * K n u) ∧
    Tendsto (fun n => ∫ u, ((H n u + c * K n u) - (Φ u + c * Ψ u)) ^ 2) atTop (𝓝 0) ∧
    ∃ M, ∀ n, (∫ u, (H n u + c * K n u) ^ 2 * Real.exp (-(8 * u))) ≤ M := by
  obtain ⟨MH, hMH⟩ := hH.weight
  obtain ⟨MK, hMK⟩ := hK.weight
  refine ⟨fun n => (hH.domain n).add_const_mul (hK.domain n) c, fun n => ?_, fun n => ?_, ?_,
    ⟨2 * MH + 2 * MK, fun n => ?_⟩⟩
  · obtain ⟨A, -, hA⟩ := hH.window n
    obtain ⟨B, -, hB⟩ := hK.window n
    exact ((hA.mono (le_max_left A B)).add_const_mul (hB.mono (le_max_right A B)) c).contDiff
  · obtain ⟨A, -, hA⟩ := hH.window n
    obtain ⟨B, -, hB⟩ := hK.window n
    exact ((hA.mono (le_max_left A B)).add_const_mul (hB.mono (le_max_right A B)) c).hasCompactSupport
  · have hb : ∀ n, (∫ u, ((H n u + c * K n u) - (Φ u + c * Ψ u)) ^ 2) ≤
        2 * (∫ u, (H n u - Φ u) ^ 2) + 2 * ∫ u, (K n u - Ψ u) ^ 2 := fun n => by
      have h := integral_sq_add_le (f := fun u => H n u - Φ u) (g := fun u => c * (K n u - Ψ u))
        (criticalHalfLineEnergyDomain_sub (hH.domain n) hΦ).sq
        (by simpa only [mul_pow] using (criticalHalfLineEnergyDomain_sub (hK.domain n) hΨ).sq.const_mul (c ^ 2))
      have e : (∫ u, (c * (K n u - Ψ u)) ^ 2) = ∫ u, (K n u - Ψ u) ^ 2 := by
        simp_rw [mul_pow, hc, one_mul]
      rw [e] at h
      refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun u => ?_)) h
      show ((H n u + c * K n u) - (Φ u + c * Ψ u)) ^ 2 = (H n u - Φ u + c * (K n u - Ψ u)) ^ 2
      ring
    have hlim := (hH.sq.const_mul 2).add (hK.sq.const_mul 2)
    rw [mul_zero, add_zero] at hlim
    exact squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) hb hlim
  · have h := integral_sq_add_le (f := fun u => H n u * Real.exp (-(4 * u)))
      (g := fun u => c * K n u * Real.exp (-(4 * u)))
      (by
        refine (hH.domain n).exponential.congr (Eventually.of_forall fun u => ?_)
        show H n u ^ 2 * Real.exp (-(8 * u)) = (H n u * Real.exp (-(4 * u))) ^ 2
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring)
      (by
        refine ((hK.domain n).exponential.const_mul (c ^ 2)).congr
          (Eventually.of_forall fun u => ?_)
        show c ^ 2 * (K n u ^ 2 * Real.exp (-(8 * u))) = (c * K n u * Real.exp (-(4 * u))) ^ 2
        rw [mul_pow, mul_pow, sq (Real.exp _), ← Real.exp_add]
        ring_nf)
    have e1 : ∀ f : ℝ → ℝ, (∫ u, (f u * Real.exp (-(4 * u))) ^ 2) =
        ∫ u, f u ^ 2 * Real.exp (-(8 * u)) := fun f =>
      integral_congr_ae (Eventually.of_forall fun u => by
        show (f u * Real.exp (-(4 * u))) ^ 2 = f u ^ 2 * Real.exp (-(8 * u))
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring)
    have e2 : (∫ u, (c * K n u * Real.exp (-(4 * u))) ^ 2) =
        ∫ u, K n u ^ 2 * Real.exp (-(8 * u)) := by
      rw [show (fun u => (c * K n u * Real.exp (-(4 * u))) ^ 2) =
          fun u => (K n u * Real.exp (-(4 * u))) ^ 2 by
        funext u; rw [mul_pow, mul_pow, mul_pow, hc, one_mul]]
      exact e1 _
    rw [e1, e2] at h
    have hsum := e1 (fun u => H n u + c * K n u)
    rw [← hsum]
    refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun u => ?_)))
      (h.trans (by linarith [hMH n, hMK n]))
    show ((H n u + c * K n u) * Real.exp (-(4 * u))) ^ 2 =
      (H n u * Real.exp (-(4 * u)) + c * K n u * Real.exp (-(4 * u))) ^ 2
    ring

/-- **Polarization.** The mixed energies of two window recoveries converge. -/
theorem IsWindowRecovery.tendsto_mixedEnergy {R : ℝ} (hR : 0 < R) {Φ Ψ : ℝ → ℝ}
    {H K : ℕ → ℝ → ℝ} (hH : IsWindowRecovery R Φ H) (hK : IsWindowRecovery R Ψ K)
    (hΦ : CriticalHalfLineEnergyDomain Φ) (hΨ : CriticalHalfLineEnergyDomain Ψ) :
    Tendsto (fun n => criticalHalfLineMixedEnergy R (H n) (K n)) atTop
      (𝓝 (criticalHalfLineMixedEnergy R Φ Ψ)) := by
  obtain ⟨hDp, hCp, hSp, hLp, ⟨Mp, hMp⟩⟩ := recovery_combination hH hK hΦ hΨ 1 (by norm_num)
  obtain ⟨hDm, hCm, hSm, hLm, ⟨Mm, hMm⟩⟩ := recovery_combination hH hK hΦ hΨ (-1) (by norm_num)
  set P : ℕ → ℝ := fun n => Q R (fun u => H n u + 1 * K n u) with hP
  set N : ℕ → ℝ := fun n => Q R (fun u => H n u + (-1) * K n u) with hN
  have ePn : ∀ n, P n = Q R (H n) + 2 * criticalHalfLineMixedEnergy R (H n) (K n) + Q R (K n) :=
    fun n => by
      rw [hP, criticalHalfLineFullEnergy_add_const_mul R (hH.domain n) (hK.domain n)]; ring
  have eNn : ∀ n, N n = Q R (H n) - 2 * criticalHalfLineMixedEnergy R (H n) (K n) + Q R (K n) :=
    fun n => by
      rw [hN, criticalHalfLineFullEnergy_add_const_mul R (hH.domain n) (hK.domain n)]; ring
  set P∞ := Q R (fun u => Φ u + 1 * Ψ u)
  set N∞ := Q R (fun u => Φ u + (-1) * Ψ u)
  have ePi : P∞ = Q R Φ + 2 * criticalHalfLineMixedEnergy R Φ Ψ + Q R Ψ := by
    rw [criticalHalfLineFullEnergy_add_const_mul R hΦ hΨ]; ring
  have eNi : N∞ = Q R Φ - 2 * criticalHalfLineMixedEnergy R Φ Ψ + Q R Ψ := by
    rw [criticalHalfLineFullEnergy_add_const_mul R hΦ hΨ]; ring
  -- bounds
  obtain ⟨CH, hCH⟩ := exists_mass_bound hH.domain hΦ hH.sq
  obtain ⟨CK, hCK⟩ := exists_mass_bound hK.domain hΨ hK.sq
  obtain ⟨UH, hUH⟩ := hH.energy.bddAbove_range
  obtain ⟨UK, hUK⟩ := hK.energy.bddAbove_range
  set μ := criticalHalfLineGroundEnergy R
  have hmass2 : ∀ n (c : ℝ), c ^ 2 = 1 →
      (∫ u, (H n u + c * K n u) ^ 2) ≤ 2 * CH + 2 * CK := fun n c hc => by
    have h := integral_sq_add_le (f := H n) (g := fun u => c * K n u) (hH.domain n).sq
      (by simpa only [mul_pow] using (hK.domain n).sq.const_mul (c ^ 2))
    have e : (∫ u, (c * K n u) ^ 2) = ∫ u, K n u ^ 2 := by simp_rw [mul_pow, hc, one_mul]
    rw [e] at h
    linarith [hCH n, hCK n]
  have hlowc : ∀ n (c : ℝ), c ^ 2 = 1 →
      -(|μ| * |2 * CH + 2 * CK|) ≤ Q R (fun u => H n u + c * K n u) := fun n c hc => by
    have h1 := criticalHalfLineGroundEnergy_mul_mass_le_all hR
      ((hH.domain n).add_const_mul (hK.domain n) c)
    have h2 := hmass2 n c hc
    have h3 : 0 ≤ ∫ u, (H n u + c * K n u) ^ 2 := integral_nonneg fun u => sq_nonneg _
    nlinarith [neg_abs_le μ, le_abs_self μ, le_abs_self (2 * CH + 2 * CK), abs_nonneg μ]
  set lo := -(|μ| * |2 * CH + 2 * CK|)
  set hi := 2 * UH + 2 * UK - lo
  have hPN : ∀ n, P n + N n = 2 * Q R (H n) + 2 * Q R (K n) := fun n => by
    rw [ePn, eNn]; ring
  have hPb : ∀ n, P n ∈ Icc lo hi := fun n => ⟨hlowc n 1 (by norm_num), by
    have := hPN n; have := hlowc n (-1) (by norm_num); have := hUH ⟨n, rfl⟩; have := hUK ⟨n, rfl⟩
    simp only [hN] at *; linarith⟩
  have hNb : ∀ n, N n ∈ Icc lo hi := fun n => ⟨hlowc n (-1) (by norm_num), by
    have := hPN n; have := hlowc n 1 (by norm_num); have := hUH ⟨n, rfl⟩; have := hUK ⟨n, rfl⟩
    simp only [hP] at *; linarith⟩
  have hsumlim : Tendsto (fun n => P n + N n) atTop (𝓝 (P∞ + N∞)) := by
    have h := (hH.energy.const_mul 2).add (hK.energy.const_mul 2)
    have e : 2 * Q R Φ + 2 * Q R Ψ = P∞ + N∞ := by rw [ePi, eNi]; ring
    rw [e] at h
    exact h.congr fun n => (hPN n).symm
  -- every subsequence has a further subsequence along which both converge to the targets
  have key : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      Tendsto (fun n => P (ns (ms n))) atTop (𝓝 P∞) ∧
        Tendsto (fun n => N (ns (ms n))) atTop (𝓝 N∞) := by
    intro ns hns
    obtain ⟨Lp, -, φ₁, hφ₁, hlim₁⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc lo hi)
      (x := fun n => P (ns n)) fun n => hPb (ns n)
    obtain ⟨Ln, -, φ₂, hφ₂, hlim₂⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc lo hi)
      (x := fun n => N (ns (φ₁ n))) fun n => hNb (ns (φ₁ n))
    have hsub : Tendsto (fun n => ns (φ₁ (φ₂ n))) atTop atTop :=
      hns.comp (hφ₁.comp hφ₂).tendsto_atTop
    have hP' : Tendsto (fun n => P (ns (φ₁ (φ₂ n)))) atTop (𝓝 Lp) :=
      hlim₁.comp hφ₂.tendsto_atTop
    have hgeP : P∞ ≤ Lp := fullEnergy_le_of_tendsto_sq hR (fun n => hDp _) (fun n => hCp _)
      (fun n => hSp _) (hΦ.add_const_mul hΨ 1) (hLp.comp hsub) (fun n => hMp _) hP'
    have hgeN : N∞ ≤ Ln := fullEnergy_le_of_tendsto_sq hR (fun n => hDm _) (fun n => hCm _)
      (fun n => hSm _) (hΦ.add_const_mul hΨ (-1)) (hLm.comp hsub) (fun n => hMm _) hlim₂
    have hsum : Lp + Ln = P∞ + N∞ :=
      tendsto_nhds_unique (hP'.add hlim₂) (hsumlim.comp hsub)
    have hp : Lp = P∞ := by linarith
    have hn : Ln = N∞ := by linarith
    exact ⟨fun n => φ₁ (φ₂ n), by rw [← hp]; exact hP', by rw [← hn]; exact hlim₂⟩
  have hPlim : Tendsto P atTop (𝓝 P∞) := tendsto_of_subseq_tendsto fun ns hns =>
    let ⟨ms, h, _⟩ := key ns hns; ⟨ms, h⟩
  have hNlim : Tendsto N atTop (𝓝 N∞) := tendsto_of_subseq_tendsto fun ns hns =>
    let ⟨ms, _, h⟩ := key ns hns; ⟨ms, h⟩
  have hmix : ∀ n, criticalHalfLineMixedEnergy R (H n) (K n) = (P n - N n) / 4 := fun n => by
    rw [ePn, eNn]; ring
  have hmixlim : criticalHalfLineMixedEnergy R Φ Ψ = (P∞ - N∞) / 4 := by
    rw [ePi, eNi]; ring
  rw [hmixlim]
  exact ((hPlim.sub hNlim).div_const 4).congr fun n => (hmix n).symm

/-! ### Negative spaces -/

/-- **Window tests carry every negative space.** If `Q_R ≤ -δ|t|²` on the span of domain profiles
`Φ_0, …, Φ_{m-1}` of mass at most one, then window tests `H_i` satisfy `Q_R ≤ -(δ/2)|t|²` on theirs. -/
theorem exists_window_family_of_negative {R : ℝ} (hR : 0 < R) {m : ℕ} {Φ : Fin m → ℝ → ℝ}
    (hΦ : ∀ i, CriticalHalfLineEnergyDomain (Φ i)) (hmass : ∀ i, (∫ u, Φ i u ^ 2) ≤ 1) {δ : ℝ}
    (hδ : 0 < δ)
    (hneg : ∀ t : Fin m → ℝ, Q R (fun u => ∑ i, t i * Φ i u) ≤ -(δ * ∑ i, t i ^ 2)) :
    ∃ H : Fin m → ℝ → ℝ, (∀ i, ∃ A, 0 ≤ A ∧ IsWindowTest A (H i)) ∧
      ∀ t : Fin m → ℝ, Q R (fun u => ∑ i, t i * H i u) ≤ -(δ / 2 * ∑ i, t i ^ 2) := by
  choose Hs hHs using fun i => exists_isWindowRecovery hR (hΦ i) (hmass i)
  set η : ℝ := δ / (2 * ((m : ℝ) + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i j, |criticalHalfLineMixedEnergy R (Hs i n) (Hs j n) -
      criticalHalfLineMixedEnergy R (Φ i) (Φ j)| ≤ η := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    have h := ((hHs i).tendsto_mixedEnergy hR (hHs j) (hΦ i) (hΦ j)).sub_const
      (criticalHalfLineMixedEnergy R (Φ i) (Φ j))
    rw [sub_self] at h
    filter_upwards [(Metric.tendsto_nhds.mp h) η hηpos] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact hn.le
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨fun i => Hs i n, fun i => (hHs i).window n, fun t => ?_⟩
  have hD : ∀ i, CriticalHalfLineEnergyDomain (Hs i n) := fun i => (hHs i).domain n
  rw [fullEnergy_finsetSum_eq R _ hD t]
  have hΦt := hneg t
  rw [fullEnergy_finsetSum_eq R _ hΦ t] at hΦt
  have hdiff : ∑ j, ∑ k, t j * t k * criticalHalfLineMixedEnergy R (Hs j n) (Hs k n) ≤
      ∑ j, ∑ k, t j * t k * criticalHalfLineMixedEnergy R (Φ j) (Φ k) +
        η * (∑ j, |t j|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := hn j k
    have e : t j * t k * criticalHalfLineMixedEnergy R (Hs j n) (Hs k n) =
        t j * t k * criticalHalfLineMixedEnergy R (Φ j) (Φ k) + t j * t k *
          (criticalHalfLineMixedEnergy R (Hs j n) (Hs k n) -
            criticalHalfLineMixedEnergy R (Φ j) (Φ k)) := by ring
    rw [e]
    have hb : t j * t k * (criticalHalfLineMixedEnergy R (Hs j n) (Hs k n) -
        criticalHalfLineMixedEnergy R (Φ j) (Φ k)) ≤ η * (|t j| * |t k|) := by
      calc _ ≤ |t j * t k * (criticalHalfLineMixedEnergy R (Hs j n) (Hs k n) -
            criticalHalfLineMixedEnergy R (Φ j) (Φ k))| := le_abs_self _
        _ = |t j| * |t k| * |criticalHalfLineMixedEnergy R (Hs j n) (Hs k n) -
            criticalHalfLineMixedEnergy R (Φ j) (Φ k)| := by rw [abs_mul, abs_mul]
        _ ≤ |t j| * |t k| * η := mul_le_mul_of_nonneg_left h (by positivity)
        _ = η * (|t j| * |t k|) := by ring
    linarith
  have hcs : (∑ j, |t j|) ^ 2 ≤ (m : ℝ) * ∑ j, t j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun j => |t j|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    exact_mod_cast h
  have hsum0 : 0 ≤ ∑ j, t j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hηm : η * ((m : ℝ) * ∑ j, t j ^ 2) ≤ δ / 2 * ∑ j, t j ^ 2 := by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hsum0
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  nlinarith [mul_le_mul_of_nonneg_left hcs hηpos.le]

#print axioms exists_window_family_of_negative

end GaloisForLFunctions.ExclusionOfTheCriticalState
