import GaloisForLFunctions.RHTower.RouteETerminalPrimeMainReduction
import GaloisForLFunctions.RHTower.RouteETerminalSourceReporterFirewall
import GaloisForLFunctions.RHTower.Sieve.FrequencySeparation

/-!
# Route E terminal-frame minimax closure

This module closes the terminal-frame card from continuous energy through literal moving primes
and every source order `0 < q ≤ 2`. It proves global compactness, odd-resonance classification,
second-order rigidity, actual constrained minimum laws, uniform Abel/PNT transport, exact source
damping stability, and physical/Fisher endpoint constants. All results are unconditional.
-/

namespace RHTower

open Filter Topology MeasureTheory Set intervalIntegral

noncomputable section

/-- Quantitative second-order coercivity near any odd terminal resonance. -/
theorem routeETerminal_secondOrderCoercivity
    {a L t u₀ : ℝ}
    (hodd : Real.cos u₀ = -1) (hsin : Real.sin u₀ = 0)
    (hres : ∀ v ∈ Icc (0 : ℝ) 1, |t * (L - v) - u₀| ≤ Real.pi) :
    4 / Real.pi ^ 2 *
        routeETerminalQuadratic a (t * L) (L * (t * L - u₀)) ≤
      L ^ 2 * routeETerminalContinuousEnergy a L t := by
  let e : ℝ → ℝ := fun v => t * (L - v) - u₀
  let b : ℝ := L * (t * L - u₀)
  let u : ℝ := t * L
  have hcontLeft : Continuous (fun v : ℝ =>
      4 / Real.pi ^ 2 *
        (routeETerminalWeight a v * (b - u * v) ^ 2)) := by
    exact continuous_const.mul
      ((continuous_routeETerminalWeight a).mul
        ((continuous_const.sub (continuous_const.mul continuous_id)).pow 2))
  have hcontRight : Continuous (fun v : ℝ =>
      L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)))) :=
    continuous_const.mul (continuous_routeETerminalContinuousIntegrand a L t)
  have hpoint : ∀ v ∈ Icc (0 : ℝ) 1,
      4 / Real.pi ^ 2 *
          (routeETerminalWeight a v * (b - u * v) ^ 2) ≤
        L ^ 2 * (routeETerminalWeight a v *
          routeETerminalPhaseEnergy t (Real.exp (L - v))) := by
    intro v hv
    have hchord := RHTower.Sieve.two_div_pi_sq_mul_sq_le_one_sub_cos
      (hres v hv)
    change 2 / Real.pi ^ 2 * (e v) ^ 2 ≤
      1 - Real.cos (e v) at hchord
    have hphase : routeETerminalPhaseEnergy t (Real.exp (L - v)) =
        2 * (1 - Real.cos (e v)) := by
      rw [routeETerminalPhaseEnergy_exp]
      rw [show t * (L - v) = u₀ + e v by dsimp [e]; ring]
      exact routeETerminalPhaseEnergy_eq_two_mul_one_sub_cos u₀ (e v) hodd hsin
    have hscaled : L * e v = b - u * v := by
      dsimp [e, b, u]
      ring
    have hw : 0 ≤ routeETerminalWeight a v := (routeETerminalWeight_pos a v).le
    rw [hphase]
    calc
      4 / Real.pi ^ 2 *
          (routeETerminalWeight a v * (b - u * v) ^ 2) =
          routeETerminalWeight a v * L ^ 2 *
            (4 / Real.pi ^ 2 * (e v) ^ 2) := by rw [← hscaled]; ring
      _ ≤ routeETerminalWeight a v * L ^ 2 *
          (2 * (1 - Real.cos (e v))) := by
        have hscaledChord : 4 / Real.pi ^ 2 * (e v) ^ 2 ≤
            2 * (1 - Real.cos (e v)) := by
          rw [show 4 / Real.pi ^ 2 * (e v) ^ 2 =
            2 * (2 / Real.pi ^ 2 * (e v) ^ 2) by ring]
          exact mul_le_mul_of_nonneg_left hchord (by norm_num)
        exact mul_le_mul_of_nonneg_left hscaledChord
          (mul_nonneg hw (sq_nonneg L))
      _ = L ^ 2 *
          (routeETerminalWeight a v * (2 * (1 - Real.cos (e v)))) := by ring
  rw [routeETerminalQuadratic, routeETerminalContinuousEnergy,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on zero_le_one
    (hcontLeft.intervalIntegrable 0 1)
    (hcontRight.intervalIntegrable 0 1) hpoint

/-- Reparameterization-invariant second-order history law. -/
theorem tendsto_routeETerminalContinuousEnergy_of_generalSecondOrderHistory
    {Z : Type*} {l : Filter Z} [l.NeBot] [l.IsCountablyGenerated]
    (a u₀ b : ℝ) (R t : Z → ℝ)
    (hodd : Real.cos u₀ = -1) (hsin : Real.sin u₀ = 0)
    (hR : Tendsto R l atTop)
    (hphase : Tendsto (fun z => t z * R z) l (nhds u₀))
    (hcorrection : Tendsto (fun z => R z * (t z * R z - u₀)) l (nhds b)) :
    Tendsto (fun z => R z ^ 2 *
      routeETerminalContinuousEnergy a (R z) (t z)) l
        (nhds (routeETerminalQuadratic a u₀ b)) := by
  let e : Z → ℝ → ℝ := fun z v => t z * (R z - v) - u₀
  let scaled : Z → ℝ → ℝ := fun z v => R z * e z v
  have hscaled (v : ℝ) : Tendsto (fun z => scaled z v) l
      (nhds (b - u₀ * v)) := by
    have hEq : (fun z => scaled z v) =
        (fun z => R z * (t z * R z - u₀) - (t z * R z) * v) := by
      funext z
      dsimp [scaled, e]
      ring
    rw [hEq]
    exact hcorrection.sub (hphase.mul_const v)
  have hRinv : Tendsto (fun z => (R z)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hR
  have hRne : ∀ᶠ z in l, R z ≠ 0 := hR.eventually (eventually_ne_atTop 0)
  have he0 (v : ℝ) : Tendsto (fun z => e z v) l (nhds 0) := by
    have hEq : ∀ᶠ z in l, e z v = scaled z v * (R z)⁻¹ := by
      filter_upwards [hRne] with z hz
      dsimp [scaled]
      field_simp
    have hEq' : (fun z => scaled z v * (R z)⁻¹) =ᶠ[l]
        (fun z => e z v) := by
      filter_upwards [hEq] with z hz
      exact hz.symm
    simpa only [mul_zero] using ((hscaled v).mul hRinv).congr' hEq'
  have hpoint (v : ℝ) : Tendsto (fun z =>
      R z ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t z) (Real.exp (R z - v)))) l
      (nhds (routeETerminalWeight a v * (b - u₀ * v) ^ 2)) := by
    have hphaseScaled := tendsto_terminalPhaseEnergy_scaled hodd hsin
      (he0 v) (hscaled v)
    have hweightLimit : Tendsto (fun _ : Z => routeETerminalWeight a v) l
        (nhds (routeETerminalWeight a v)) := tendsto_const_nhds
    have hmul := hweightLimit.mul hphaseScaled
    have hEq : (fun z => routeETerminalWeight a v *
        (R z ^ 2 * (2 + 2 * Real.cos (u₀ + e z v)))) =
        (fun z => R z ^ 2 * (routeETerminalWeight a v *
          routeETerminalPhaseEnergy (t z) (Real.exp (R z - v)))) := by
      funext z
      rw [routeETerminalPhaseEnergy_exp]
      rw [show t z * (R z - v) = u₀ + e z v by dsimp [e]; ring]
      ring
    have ht := hmul.congr'
      (Filter.Eventually.of_forall fun z => congrFun hEq z)
    simpa using ht
  let B : ℝ := |b| + |u₀| + 2
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hcorrAbs : ∀ᶠ z in l,
      |R z * (t z * R z - u₀)| < |b| + 1 := by
    have habs : Tendsto (fun z => |R z * (t z * R z - u₀)|) l (nhds |b|) :=
      (continuous_abs.tendsto b).comp hcorrection
    exact (tendsto_order.1 habs).2 (|b| + 1) (by linarith)
  have hphaseAbs : ∀ᶠ z in l, |t z * R z| < |u₀| + 1 := by
    have habs : Tendsto (fun z => |t z * R z|) l (nhds |u₀|) :=
      (continuous_abs.tendsto u₀).comp hphase
    exact (tendsto_order.1 habs).2 (|u₀| + 1) (by linarith)
  have hbound : ∀ᶠ z in l, ∀ᵐ v : ℝ,
      v ∈ uIoc (0 : ℝ) 1 →
      ‖R z ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t z) (Real.exp (R z - v)))‖ ≤
        routeETerminalWeight a v * B ^ 2 := by
    filter_upwards [hcorrAbs, hphaseAbs] with z hcorr hphaseZ
    filter_upwards with v hv
    rw [uIoc_of_le zero_le_one] at hv
    have hvabs : |v| ≤ 1 := by rw [abs_of_nonneg hv.1.le]; exact hv.2
    have hscaledBound : |scaled z v| ≤ B := by
      have hEq : scaled z v =
          R z * (t z * R z - u₀) - (t z * R z) * v := by
        dsimp [scaled, e]
        ring
      rw [hEq]
      calc
        |R z * (t z * R z - u₀) - (t z * R z) * v| ≤
            |R z * (t z * R z - u₀)| + |(t z * R z) * v| := abs_sub _ _
        _ = |R z * (t z * R z - u₀)| + |t z * R z| * |v| := by
          simp only [abs_mul]
        _ ≤ (|b| + 1) + (|u₀| + 1) * 1 := by
          exact add_le_add hcorr.le
            (mul_le_mul hphaseZ.le hvabs (abs_nonneg _) (by positivity))
        _ = B := by dsimp [B]; ring
    have hrewrite : routeETerminalPhaseEnergy (t z) (Real.exp (R z - v)) =
        2 * (1 - Real.cos (e z v)) := by
      rw [routeETerminalPhaseEnergy_exp]
      rw [show t z * (R z - v) = u₀ + e z v by dsimp [e]; ring]
      exact routeETerminalPhaseEnergy_eq_two_mul_one_sub_cos
        u₀ (e z v) hodd hsin
    rw [hrewrite, Real.norm_eq_abs]
    have hphaseNonneg : 0 ≤ 2 * (1 - Real.cos (e z v)) := by
      nlinarith [Real.cos_le_one (e z v)]
    have hnonneg : 0 ≤ R z ^ 2 *
        (routeETerminalWeight a v * (2 * (1 - Real.cos (e z v)))) :=
      mul_nonneg (sq_nonneg _)
        (mul_nonneg (routeETerminalWeight_pos a v).le hphaseNonneg)
    rw [abs_of_nonneg hnonneg]
    have hphaseLe : 2 * (1 - Real.cos (e z v)) ≤ (e z v) ^ 2 := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := e z v)]
    have hsq : (scaled z v) ^ 2 ≤ B ^ 2 := by
      apply (sq_le_sq).2
      rwa [abs_of_pos hBpos]
    calc
      R z ^ 2 * (routeETerminalWeight a v *
          (2 * (1 - Real.cos (e z v)))) ≤
          R z ^ 2 * (routeETerminalWeight a v * (e z v) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hphaseLe
            (routeETerminalWeight_pos a v).le) (sq_nonneg _)
      _ = routeETerminalWeight a v * (scaled z v) ^ 2 := by
        dsimp [scaled]
        ring
      _ ≤ routeETerminalWeight a v * B ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (routeETerminalWeight_pos a v).le
  have hboundInt : IntervalIntegrable (fun v : ℝ =>
      routeETerminalWeight a v * B ^ 2) volume 0 1 :=
    ((continuous_routeETerminalWeight a).mul continuous_const).intervalIntegrable 0 1
  have hmeas (z : Z) : AEStronglyMeasurable (fun v : ℝ =>
      R z ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t z) (Real.exp (R z - v))))
      (volume.restrict (uIoc (0 : ℝ) 1)) :=
    ((continuous_const.mul
      (continuous_routeETerminalContinuousIntegrand a (R z) (t z))).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun v : ℝ => routeETerminalWeight a v * B ^ 2)
    (l := l)
    (F := fun z v => R z ^ 2 * (routeETerminalWeight a v *
      routeETerminalPhaseEnergy (t z) (Real.exp (R z - v))))
    (f := fun v => routeETerminalWeight a v * (b - u₀ * v) ^ 2)
    (Eventually.of_forall hmeas) hbound hboundInt
    (Eventually.of_forall fun v _ => hpoint v)
  have hleft : ∀ z : Z,
      (∫ v in (0 : ℝ)..1, R z ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t z) (Real.exp (R z - v)))) =
      R z ^ 2 * routeETerminalContinuousEnergy a (R z) (t z) := by
    intro z
    rw [routeETerminalContinuousEnergy, intervalIntegral.integral_const_mul]
  simpa only [hleft, routeETerminalQuadratic] using hDCT

@[simp] theorem routeETerminalContinuousEnergy_zero_frequency (a L : ℝ) :
    routeETerminalContinuousEnergy a L 0 = 4 * routeETerminalMass a := by
  rw [routeETerminalContinuousEnergy, routeETerminalMass,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  change routeETerminalWeight a v *
    routeETerminalPhaseEnergy 0 (Real.exp (L - v)) =
      4 * routeETerminalWeight a v
  rw [routeETerminalPhaseEnergy_exp]
  simp
  ring

/-- Compactness classification of every convergent finite-energy history. -/
theorem routeETerminalContinuousEnergy_limit_compactness
    (a Q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (R t : ℕ → ℝ)
    (hR : Tendsto R atTop atTop)
    (henergy : Tendsto (fun n => R n ^ 2 *
      routeETerminalContinuousEnergy a (R n) (t n)) atTop (nhds Q)) :
    Real.pi ^ 2 * routeETerminalVariance a ≤ Q ∧
      ∃ u₀ b₀ : ℝ, ∃ χ : ℕ → ℕ,
        Tendsto χ atTop atTop ∧
        Real.cos u₀ = -1 ∧ Real.sin u₀ = 0 ∧
        Real.pi ^ 2 ≤ u₀ ^ 2 ∧
        Tendsto (fun n => t (χ n) * R (χ n)) atTop (nhds u₀) ∧
        Tendsto (fun n => R (χ n) * (t (χ n) * R (χ n) - u₀))
          atTop (nhds b₀) ∧
        Q = routeETerminalQuadratic a u₀ b₀ := by
  let E : ℕ → ℝ := fun n => R n ^ 2 *
    routeETerminalContinuousEnergy a (R n) (t n)
  let u : ℕ → ℝ := fun n => t n * R n
  let C : ℝ := |Q| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hEle : ∀ᶠ n in atTop, E n ≤ C := by
    have habs : Tendsto (fun n => |E n|) atTop (nhds |Q|) :=
      (continuous_abs.tendsto Q).comp (by simpa [E] using henergy)
    have hlt : ∀ᶠ n in atTop, |E n| < C :=
      (tendsto_order.1 habs).2 C (by dsimp [C]; linarith)
    filter_upwards [hlt] with n hn
    exact (le_abs_self (E n)).trans hn.le
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_routeETerminal_boundedEnergy_localization_constant
  have hsqTop : Tendsto (fun n => R n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hR
  have hthresholdTop : Tendsto (fun n => R n ^ 2 * δ) atTop atTop :=
    hsqTop.atTop_mul_const hδ
  have hthreshold : ∀ᶠ n in atTop, C < R n ^ 2 * δ :=
    hthresholdTop.eventually_gt_atTop C
  have hRone : ∀ᶠ n in atTop, 1 ≤ R n := hR.eventually_ge_atTop 1
  let K : ℝ := 14 * Real.exp 1 * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have huSq : ∀ᶠ n in atTop, u n ^ 2 ≤ K := by
    filter_upwards [hEle, hthreshold, hRone] with n hEn hth hRn
    have hloc := hlocal a (R n) (t n) C ha0 ha1 hRn hC.le
      (by simpa [E] using hEn) hth
    simpa [u, K, mul_comm, mul_pow, sq_abs] using hloc
  obtain ⟨N, hN⟩ := eventually_atTop.1 huSq
  let B : ℝ := K + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have huMem (n : ℕ) : u (n + N) ∈ Icc (-B) B := by
    have hs := hN (n + N) (by omega)
    have huUpper : u (n + N) ≤ B := by
      nlinarith [sq_nonneg (u (n + N) - 1)]
    have huLower : -B ≤ u (n + N) := by
      nlinarith [sq_nonneg (u (n + N) + 1)]
    exact ⟨huLower, huUpper⟩
  obtain ⟨u₀, hu₀Mem, φ, hφ, hu₀⟩ :=
    isCompact_Icc.tendsto_subseq huMem
  let ψ : ℕ → ℕ := fun n => φ n + N
  have hψ : Tendsto ψ atTop atTop := by
    exact (hφ.add_const N).tendsto_atTop
  have huLimit : Tendsto (fun n => u (ψ n)) atTop (nhds u₀) := by
    simpa [Function.comp_def, ψ, add_comm] using hu₀
  have hRψ : Tendsto (fun n => R (ψ n)) atTop atTop := hR.comp hψ
  have henergyE : Tendsto E atTop (nhds Q) := by
    simpa [E] using henergy
  have henergyψ : Tendsto (fun n => E (ψ n)) atTop (nhds Q) :=
    henergyE.comp hψ
  have hRψinv : Tendsto (fun n => (R (ψ n))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hRψ
  have htZero : Tendsto (fun n => t (ψ n)) atTop (nhds 0) := by
    have hprod := huLimit.mul hRψinv
    have heq : ∀ᶠ n in atTop,
        u (ψ n) * (R (ψ n))⁻¹ = t (ψ n) := by
      filter_upwards [hRψ.eventually (eventually_ne_atTop 0)] with n hn
      dsimp [u]
      field_simp
    simpa using hprod.congr' heq
  have hrawEnergyZero : Tendsto (fun n =>
      routeETerminalContinuousEnergy a (R (ψ n)) (t (ψ n)))
      atTop (nhds 0) := by
    have hinvSq := hRψinv.pow 2
    have hprod := henergyψ.mul hinvSq
    have heq : ∀ᶠ n in atTop,
        E (ψ n) * ((R (ψ n))⁻¹) ^ 2 =
          routeETerminalContinuousEnergy a (R (ψ n)) (t (ψ n)) := by
      filter_upwards [hRψ.eventually (eventually_ne_atTop 0)] with n hn
      dsimp [E]
      field_simp
    simpa using hprod.congr' heq
  have htNe : ∀ᶠ n in atTop, t (ψ n) ≠ 0 := by
    have hsmall : ∀ᶠ n in atTop,
        routeETerminalContinuousEnergy a (R (ψ n)) (t (ψ n)) <
          2 * routeETerminalMass a := by
      exact (tendsto_order.1 hrawEnergyZero).2 _
        (by positivity [routeETerminalMass_pos a])
    filter_upwards [hsmall] with n hn hzero
    rw [hzero, routeETerminalContinuousEnergy_zero_frequency] at hn
    linarith [routeETerminalMass_pos a]
  have hoddClass := routeETerminal_oddResonance_of_vanishingEnergy
    (l := (atTop : Filter ℕ))
    (a := fun _ => a) (L := fun n => R (ψ n)) (t := fun n => t (ψ n))
    (u := u₀)
    (Eventually.of_forall fun _ => ha0)
    (Eventually.of_forall fun _ => ha1)
    htNe htZero (by simpa [u] using huLimit) hrawEnergyZero
  obtain ⟨k, hk⟩ := hoddClass
  have hodd : Real.cos u₀ = -1 := Real.cos_eq_neg_one_iff.mpr ⟨k, hk⟩
  have hsin : Real.sin u₀ = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq u₀]
  have huClose : ∀ᶠ n in atTop, |u (ψ n) - u₀| < Real.pi / 2 := by
    obtain ⟨Nu, hNu⟩ := Metric.tendsto_atTop.1 huLimit
      (Real.pi / 2) (by positivity [Real.pi_pos])
    exact eventually_atTop.2 ⟨Nu, fun n hn => by
      simpa only [Real.dist_eq] using hNu n hn⟩
  have htClose : ∀ᶠ n in atTop, |t (ψ n)| < Real.pi / 2 := by
    obtain ⟨Nt, hNt⟩ := Metric.tendsto_atTop.1 htZero
      (Real.pi / 2) (by positivity [Real.pi_pos])
    exact eventually_atTop.2 ⟨Nt, fun n hn => by
      simpa only [Real.dist_eq, sub_zero] using hNt n hn⟩
  have hres : ∀ᶠ n in atTop, ∀ v ∈ Icc (0 : ℝ) 1,
      |t (ψ n) * (R (ψ n) - v) - u₀| ≤ Real.pi := by
    filter_upwards [huClose, htClose] with n hun htn v hv
    have hvabs : |v| ≤ 1 := by
      rw [abs_of_nonneg hv.1]
      exact hv.2
    have hrewrite :
        t (ψ n) * (R (ψ n) - v) - u₀ =
          (u (ψ n) - u₀) - t (ψ n) * v := by
      dsimp [u]
      ring
    rw [hrewrite]
    calc
      |(u (ψ n) - u₀) - t (ψ n) * v| ≤
          |u (ψ n) - u₀| + |t (ψ n) * v| := abs_sub _ _
      _ = |u (ψ n) - u₀| + |t (ψ n)| * |v| := by rw [abs_mul]
      _ ≤ |u (ψ n) - u₀| + |t (ψ n)| := by
        exact add_le_add le_rfl
          (mul_le_of_le_one_right (abs_nonneg _) hvabs)
      _ ≤ Real.pi := by linarith
  have hEψle : ∀ᶠ n in atTop, E (ψ n) ≤ C := by
    exact hψ.eventually hEle
  let c : ℝ := 4 / Real.pi ^ 2
  have hc : 0 < c := by dsimp [c]; positivity [Real.pi_pos]
  let M : ℝ := C / c
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let bseq : ℕ → ℝ := fun n =>
    R (ψ n) * (u (ψ n) - u₀)
  have hquadLe : ∀ᶠ n in atTop,
      routeETerminalQuadratic a (u (ψ n)) (bseq n) ≤ M := by
    filter_upwards [hres, hEψle] with n hresn hEn
    have hcoercive := routeETerminal_secondOrderCoercivity
      (a := a) (L := R (ψ n)) (t := t (ψ n)) (u₀ := u₀)
      hodd hsin hresn
    have hmain : c * routeETerminalQuadratic a (u (ψ n)) (bseq n) ≤ C := by
      simpa [c, bseq, u, E] using hcoercive.trans hEn
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmain)
  let D : ℝ := M / routeETerminalMass a
  have hD : 0 ≤ D := by
    exact div_nonneg hM (routeETerminalMass_pos a).le
  have huAbs : ∀ᶠ n in atTop, |u (ψ n)| < |u₀| + 1 := by
    have habs : Tendsto (fun n => |u (ψ n)|) atTop (nhds |u₀|) :=
      (continuous_abs.tendsto u₀).comp huLimit
    exact (tendsto_order.1 habs).2 _ (by linarith)
  have hcenterSq : ∀ᶠ n in atTop,
      (bseq n - u (ψ n) * routeETerminalMean a) ^ 2 ≤ D := by
    filter_upwards [hquadLe] with n hqn
    have hpyth := routeETerminalQuadratic_eq_variance_add_centering
      a (u (ψ n)) (bseq n)
    have hcenterMass : routeETerminalMass a *
        (bseq n - u (ψ n) * routeETerminalMean a) ^ 2 ≤ M := by
      rw [hpyth] at hqn
      nlinarith [mul_nonneg (sq_nonneg (u (ψ n)))
        (routeETerminalVariance_pos a).le]
    exact (le_div_iff₀ (routeETerminalMass_pos a)).2
      (by simpa [mul_comm] using hcenterMass)
  let Bcorr : ℝ :=
    Real.sqrt D + (|u₀| + 1) * |routeETerminalMean a| + 1
  have hBcorr : 0 < Bcorr := by dsimp [Bcorr]; positivity
  have hbAbs : ∀ᶠ n in atTop, |bseq n| ≤ Bcorr := by
    filter_upwards [hcenterSq, huAbs] with n hcenter hun
    have hcenterAbs :
        |bseq n - u (ψ n) * routeETerminalMean a| ≤ Real.sqrt D := by
      rw [Real.le_sqrt (abs_nonneg _) hD]
      simpa [sq_abs] using hcenter
    calc
      |bseq n| = |(bseq n - u (ψ n) * routeETerminalMean a) +
          u (ψ n) * routeETerminalMean a| := by congr 1; ring
      _ ≤ |bseq n - u (ψ n) * routeETerminalMean a| +
          |u (ψ n) * routeETerminalMean a| := abs_add_le _ _
      _ ≤ Real.sqrt D +
          (|u₀| + 1) * |routeETerminalMean a| := by
        rw [abs_mul]
        exact add_le_add hcenterAbs
          (mul_le_mul_of_nonneg_right hun.le (abs_nonneg _))
      _ ≤ Bcorr := by dsimp [Bcorr]; linarith
  obtain ⟨Ncorr, hNcorr⟩ := eventually_atTop.1 hbAbs
  have hbMem (n : ℕ) : bseq (n + Ncorr) ∈ Icc (-Bcorr) Bcorr := by
    exact abs_le.1 (hNcorr (n + Ncorr) (by omega))
  obtain ⟨b₀, hb₀Mem, φcorr, hφcorr, hb₀⟩ :=
    isCompact_Icc.tendsto_subseq hbMem
  let ρ : ℕ → ℕ := fun n => φcorr n + Ncorr
  have hρ : Tendsto ρ atTop atTop :=
    (hφcorr.add_const Ncorr).tendsto_atTop
  let χ : ℕ → ℕ := fun n => ψ (ρ n)
  have hχ : Tendsto χ atTop atTop := hψ.comp hρ
  have huχ : Tendsto (fun n => u (χ n)) atTop (nhds u₀) := by
    simpa [χ, Function.comp_def] using huLimit.comp hρ
  have hRχ : Tendsto (fun n => R (χ n)) atTop atTop := hR.comp hχ
  have hbχ : Tendsto (fun n =>
      R (χ n) * (u (χ n) - u₀)) atTop (nhds b₀) := by
    simpa [Function.comp_def, χ, ρ, bseq, add_comm] using hb₀
  have henergyχ : Tendsto (fun n => E (χ n)) atTop (nhds Q) :=
    henergyE.comp hχ
  have hsecond : Tendsto (fun n => E (χ n)) atTop
      (nhds (routeETerminalQuadratic a u₀ b₀)) := by
    simpa [E, u] using
      tendsto_routeETerminalContinuousEnergy_of_generalSecondOrderHistory
        a u₀ b₀ (fun n => R (χ n)) (fun n => t (χ n))
        hodd hsin hRχ (by simpa [u] using huχ) (by simpa [u] using hbχ)
  have hQ : Q = routeETerminalQuadratic a u₀ b₀ :=
    tendsto_nhds_unique henergyχ hsecond
  have hpiSq : Real.pi ^ 2 ≤ u₀ ^ 2 := by
    rw [← hk]
    by_cases hk0 : 0 ≤ k
    · have hk0' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
      have hterm : 0 ≤ (k : ℝ) * (2 * Real.pi) := by positivity
      have hexpr0 : 0 ≤ Real.pi + (k : ℝ) * (2 * Real.pi) :=
        add_nonneg Real.pi_pos.le hterm
      exact (sq_le_sq₀ Real.pi_pos.le hexpr0).2 (by linarith)
    · have hkneg : k ≤ -1 := by omega
      have hkneg' : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg
      have hterm : (k : ℝ) * (2 * Real.pi) ≤ (-1 : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hkneg' (by positivity [Real.pi_pos])
      have hneg : Real.pi ≤ -(Real.pi + (k : ℝ) * (2 * Real.pi)) := by
        linarith
      have hminus0 : 0 ≤ -(Real.pi + (k : ℝ) * (2 * Real.pi)) :=
        Real.pi_pos.le.trans hneg
      simpa only [neg_sq] using
        (sq_le_sq₀ Real.pi_pos.le hminus0).2 hneg
  have hlower : Real.pi ^ 2 * routeETerminalVariance a ≤ Q := by
    calc
    Real.pi ^ 2 * routeETerminalVariance a ≤
        u₀ ^ 2 * routeETerminalVariance a :=
      mul_le_mul_of_nonneg_right hpiSq (routeETerminalVariance_pos a).le
    _ ≤ routeETerminalQuadratic a u₀ b₀ :=
      routeETerminalVariance_minimax_lower a u₀ b₀
    _ = Q := hQ.symm
  refine ⟨hlower, u₀, b₀, χ, hχ, hodd, hsin, hpiSq, ?_, ?_, hQ⟩
  · simpa [u] using huχ
  · simpa [u] using hbχ

/-- Every convergent finite-energy history has limit at least first odd-resonance variance. -/
theorem routeETerminalContinuousEnergy_limit_ge_firstOdd
    (a Q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (R t : ℕ → ℝ)
    (hR : Tendsto R atTop atTop)
    (henergy : Tendsto (fun n => R n ^ 2 *
      routeETerminalContinuousEnergy a (R n) (t n)) atTop (nhds Q)) :
    Real.pi ^ 2 * routeETerminalVariance a ≤ Q :=
  (routeETerminalContinuousEnergy_limit_compactness
    a Q ha0 ha1 R t hR henergy).1

/-- Sharp histories have only two possible first-resonance signs, and their second-order
correction is uniquely terminal-position centered. -/
theorem routeETerminal_asymptoticMinimizer_sign_subsequence
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (R t : ℕ → ℝ)
    (hR : Tendsto R atTop atTop)
    (henergy : Tendsto (fun n => R n ^ 2 *
      routeETerminalContinuousEnergy a (R n) (t n)) atTop
        (nhds (Real.pi ^ 2 * routeETerminalVariance a))) :
    ∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
      ((Tendsto (fun n => t (χ n) * R (χ n)) atTop (nhds Real.pi) ∧
        Tendsto (fun n => R (χ n) *
          (t (χ n) * R (χ n) - Real.pi)) atTop
            (nhds (Real.pi * routeETerminalMean a))) ∨
       (Tendsto (fun n => t (χ n) * R (χ n)) atTop (nhds (-Real.pi)) ∧
        Tendsto (fun n => R (χ n) *
          (t (χ n) * R (χ n) - (-Real.pi))) atTop
            (nhds ((-Real.pi) * routeETerminalMean a)))) := by
  obtain ⟨hlower, u₀, b₀, χ, hχ, hodd, hsin, hpiSq, hphase, hcorr, hQ⟩ :=
    routeETerminalContinuousEnergy_limit_compactness a
      (Real.pi ^ 2 * routeETerminalVariance a) ha0 ha1 R t hR henergy
  have huSqUpper : u₀ ^ 2 ≤ Real.pi ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (routeETerminalVariance_pos a)).mp
    exact calc
      u₀ ^ 2 * routeETerminalVariance a ≤
          routeETerminalQuadratic a u₀ b₀ :=
        routeETerminalVariance_minimax_lower a u₀ b₀
      _ = Real.pi ^ 2 * routeETerminalVariance a := hQ.symm
  have huSq : u₀ ^ 2 = Real.pi ^ 2 := le_antisymm huSqUpper hpiSq
  have hb₀ : b₀ = u₀ * routeETerminalMean a := by
    apply (routeETerminalVariance_minimax_eq_iff a u₀ b₀).mp
    calc
      routeETerminalQuadratic a u₀ b₀ =
          Real.pi ^ 2 * routeETerminalVariance a := hQ.symm
      _ = u₀ ^ 2 * routeETerminalVariance a := by rw [huSq]
  refine ⟨χ, hχ, ?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp huSq with hu | hu
  · left
    subst u₀
    subst b₀
    exact ⟨hphase, hcorr⟩
  · right
    have hu' : u₀ = -Real.pi := hu
    subst u₀
    subst b₀
    exact ⟨hphase, hcorr⟩

/-- Energy is continuous in frequency, so compact frequency windows have genuine minimizers. -/
theorem continuous_routeETerminalContinuousEnergy_frequency (a L : ℝ) :
    Continuous (fun t => routeETerminalContinuousEnergy a L t) := by
  unfold routeETerminalContinuousEnergy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  rw [show Function.uncurry (fun t v : ℝ =>
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v))) =
      fun z : ℝ × ℝ => Real.exp (-a * z.2) *
        (2 + 2 * Real.cos (z.1 * (L - z.2))) by
      funext z
      change routeETerminalWeight a z.2 *
          routeETerminalPhaseEnergy z.1 (Real.exp (L - z.2)) = _
      rw [routeETerminalWeight, routeETerminalPhaseEnergy_exp]]
  fun_prop

/-- Subexponential terminal frequency radius used by prime PNT transport. -/
noncomputable def routeETerminalFrequencyRadius (κ L : ℝ) : ℝ :=
  Real.exp (κ * Real.sqrt L)

theorem routeETerminalFrequencyRadius_pos (κ L : ℝ) :
    0 < routeETerminalFrequencyRadius κ L := by
  exact Real.exp_pos _

theorem exists_routeETerminalConstrainedMinimizer (a κ L : ℝ) :
    ∃ t ∈ Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L),
      IsMinOn (fun s => routeETerminalContinuousEnergy a L s)
        (Icc (-routeETerminalFrequencyRadius κ L)
          (routeETerminalFrequencyRadius κ L)) t := by
  have hne : (Icc (-routeETerminalFrequencyRadius κ L)
      (routeETerminalFrequencyRadius κ L)).Nonempty :=
    nonempty_Icc.mpr (by linarith [routeETerminalFrequencyRadius_pos κ L])
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (continuous_routeETerminalContinuousEnergy_frequency a L).continuousOn
  exact ⟨t, ht, hmin⟩

noncomputable def routeETerminalConstrainedMinimizer (a κ L : ℝ) : ℝ :=
  Classical.choose (exists_routeETerminalConstrainedMinimizer a κ L)

noncomputable def routeETerminalConstrainedMinimum (a κ L : ℝ) : ℝ :=
  routeETerminalContinuousEnergy a L
    (routeETerminalConstrainedMinimizer a κ L)

theorem routeETerminalConstrainedMinimizer_mem (a κ L : ℝ) :
    routeETerminalConstrainedMinimizer a κ L ∈
      Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L) :=
  (Classical.choose_spec (exists_routeETerminalConstrainedMinimizer a κ L)).1

theorem routeETerminalConstrainedMinimum_le
    (a κ L t : ℝ)
    (ht : t ∈ Icc (-routeETerminalFrequencyRadius κ L)
      (routeETerminalFrequencyRadius κ L)) :
    routeETerminalConstrainedMinimum a κ L ≤
      routeETerminalContinuousEnergy a L t := by
  exact (isMinOn_iff.mp
    (Classical.choose_spec (exists_routeETerminalConstrainedMinimizer a κ L)).2) t ht

theorem routeETerminalConstrainedMinimum_nonneg (a κ L : ℝ) :
    0 ≤ routeETerminalConstrainedMinimum a κ L :=
  routeETerminalContinuousEnergy_nonneg _ _ _

private theorem tendsto_routeETerminalCenteredFirstOdd_frequency_zero (a : ℝ) :
    Tendsto (fun L : ℝ => Real.pi / L +
      Real.pi * routeETerminalMean a / L ^ 2) atTop (nhds 0) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun L : ℝ => (L ^ 2)⁻¹) atTop (nhds 0) := by
    simpa [inv_pow] using hinv.pow 2
  simpa [div_eq_mul_inv] using
    (hinv.const_mul Real.pi).add
      (hinv2.const_mul (Real.pi * routeETerminalMean a))

private theorem eventually_routeETerminalCenteredFirstOdd_mem
    (a κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop,
      Real.pi / L + Real.pi * routeETerminalMean a / L ^ 2 ∈
        Icc (-routeETerminalFrequencyRadius κ L)
          (routeETerminalFrequencyRadius κ L) := by
  have hsmall : ∀ᶠ L : ℝ in atTop,
      |Real.pi / L + Real.pi * routeETerminalMean a / L ^ 2| < 1 := by
    obtain ⟨A, hA⟩ := Metric.tendsto_atTop.1
      (tendsto_routeETerminalCenteredFirstOdd_frequency_zero a) 1 zero_lt_one
    exact eventually_atTop.2 ⟨A, fun L hL => by
      simpa only [Real.dist_eq, sub_zero] using hA L hL⟩
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with L htrial hL
  have hradius : 1 ≤ routeETerminalFrequencyRadius κ L := by
    rw [routeETerminalFrequencyRadius, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hκ.le (Real.sqrt_nonneg L))
  exact abs_le.1 (htrial.le.trans hradius)

/-- Sequential closure upgrades to eventual sharp lower bound for genuine compact-window
minima. This is global in frequency: no near-resonance hypothesis is assumed. -/
theorem eventually_routeETerminalConstrainedMinimum_lower
    (a κ b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : b < Real.pi ^ 2 * routeETerminalVariance a) :
    ∀ᶠ L : ℝ in atTop,
      b < L ^ 2 * routeETerminalConstrainedMinimum a κ L := by
  classical
  by_cases hb0 : b < 0
  · filter_upwards with L
    exact hb0.trans_le (mul_nonneg (sq_nonneg L)
      (routeETerminalConstrainedMinimum_nonneg a κ L))
  have hb0' : 0 ≤ b := le_of_not_gt hb0
  by_contra hnot
  have hfrequent : ∃ᶠ L : ℝ in atTop,
      L ^ 2 * routeETerminalConstrainedMinimum a κ L ≤ b := by
    simpa only [not_eventually, not_lt] using hnot
  have hexists (n : ℕ) : ∃ L : ℝ, (n : ℝ) ≤ L ∧
      L ^ 2 * routeETerminalConstrainedMinimum a κ L ≤ b := by
    obtain ⟨L, hbad, hlarge⟩ :=
      (hfrequent.and_eventually (eventually_ge_atTop (n : ℝ))).exists
    exact ⟨L, hlarge, hbad⟩
  let R : ℕ → ℝ := fun n => Classical.choose (hexists n)
  have hRlower (n : ℕ) : (n : ℝ) ≤ R n :=
    (Classical.choose_spec (hexists n)).1
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall hRlower)
      tendsto_natCast_atTop_atTop
  let t : ℕ → ℝ := fun n => routeETerminalConstrainedMinimizer a κ (R n)
  let En : ℕ → ℝ := fun n => R n ^ 2 *
    routeETerminalContinuousEnergy a (R n) (t n)
  have hEnLe (n : ℕ) : En n ≤ b := by
    dsimp [En, t, R]
    simpa [routeETerminalConstrainedMinimum] using
      (Classical.choose_spec (hexists n)).2
  have hEnMem (n : ℕ) : En n ∈ Icc (0 : ℝ) b := by
    exact ⟨mul_nonneg (sq_nonneg _) (routeETerminalContinuousEnergy_nonneg _ _ _),
      hEnLe n⟩
  obtain ⟨Q, hQmem, φ, hφ, hQ⟩ :=
    isCompact_Icc.tendsto_subseq hEnMem
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hRφ : Tendsto (fun n => R (φ n)) atTop atTop := hR.comp hφtop
  have henergyφ : Tendsto (fun n => R (φ n) ^ 2 *
      routeETerminalContinuousEnergy a (R (φ n)) (t (φ n)))
      atTop (nhds Q) := by
    simpa [Function.comp_def, En] using hQ
  have hlower := routeETerminalContinuousEnergy_limit_ge_firstOdd
    a Q ha0 ha1 (fun n => R (φ n)) (fun n => t (φ n)) hRφ henergyφ
  exact (not_lt_of_ge hlower) (hQmem.2.trans_lt hb)

/-- Exact continuous terminal-band minimax law on every positive subexponential frequency
window. -/
theorem tendsto_routeETerminalConstrainedMinimum
    (a κ : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ : 0 < κ) :
    Tendsto (fun L : ℝ => L ^ 2 *
      routeETerminalConstrainedMinimum a κ L) atTop
        (nhds (Real.pi ^ 2 * routeETerminalVariance a)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact eventually_routeETerminalConstrainedMinimum_lower a κ b ha0 ha1 hb
  · intro b hb
    have htrial := tendsto_routeETerminalContinuousEnergy_centeredFirstOdd a
    have htrialUpper : ∀ᶠ L : ℝ in atTop,
        L ^ 2 * routeETerminalContinuousEnergy a L
          (Real.pi / L + Real.pi * routeETerminalMean a / L ^ 2) < b :=
      (tendsto_order.1 htrial).2 b hb
    filter_upwards [eventually_routeETerminalCenteredFirstOdd_mem a κ hκ,
      htrialUpper] with L hmem hupper
    exact (mul_le_mul_of_nonneg_left
      (routeETerminalConstrainedMinimum_le a κ L _ hmem) (sq_nonneg L)).trans_lt hupper

/-! ## Literal moving-prime minimax closure -/

theorem continuous_routeETerminalPrimeFrame_frequency (r X : ℝ) :
    Continuous (fun t => routeETerminalPrimeFrame r X t) := by
  unfold routeETerminalPrimeFrame
  refine continuous_finsetSum _ fun k hk => ?_
  by_cases hp : k.Prime
  · simp only [hp, if_true]
    unfold routeETerminalPhaseEnergy
    fun_prop
  · simp only [hp, if_false]
    exact continuous_const

theorem exists_routeETerminalPrimeConstrainedMinimizer (r κ L : ℝ) :
    ∃ t ∈ Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L),
      IsMinOn (fun s => routeETerminalPrimeFrame r (Real.exp L) s)
        (Icc (-routeETerminalFrequencyRadius κ L)
          (routeETerminalFrequencyRadius κ L)) t := by
  have hne : (Icc (-routeETerminalFrequencyRadius κ L)
      (routeETerminalFrequencyRadius κ L)).Nonempty :=
    nonempty_Icc.mpr (by linarith [routeETerminalFrequencyRadius_pos κ L])
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (continuous_routeETerminalPrimeFrame_frequency r (Real.exp L)).continuousOn
  exact ⟨t, ht, hmin⟩

noncomputable def routeETerminalPrimeConstrainedMinimizer
    (r κ L : ℝ) : ℝ :=
  Classical.choose (exists_routeETerminalPrimeConstrainedMinimizer r κ L)

noncomputable def routeETerminalPrimeConstrainedMinimum
    (r κ L : ℝ) : ℝ :=
  routeETerminalPrimeFrame r (Real.exp L)
    (routeETerminalPrimeConstrainedMinimizer r κ L)

theorem routeETerminalPrimeConstrainedMinimizer_mem (r κ L : ℝ) :
    routeETerminalPrimeConstrainedMinimizer r κ L ∈
      Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L) :=
  (Classical.choose_spec
    (exists_routeETerminalPrimeConstrainedMinimizer r κ L)).1

theorem routeETerminalPrimeConstrainedMinimum_le
    (r κ L t : ℝ)
    (ht : t ∈ Icc (-routeETerminalFrequencyRadius κ L)
      (routeETerminalFrequencyRadius κ L)) :
    routeETerminalPrimeConstrainedMinimum r κ L ≤
      routeETerminalPrimeFrame r (Real.exp L) t := by
  exact (isMinOn_iff.mp (Classical.choose_spec
    (exists_routeETerminalPrimeConstrainedMinimizer r κ L)).2) t ht

theorem routeETerminalPrimeConstrainedMinimum_nonneg (r κ L : ℝ) :
    0 ≤ routeETerminalPrimeConstrainedMinimum r κ L := by
  rw [routeETerminalPrimeConstrainedMinimum, routeETerminalPrimeFrame]
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      (routeETerminalPhaseEnergy_nonneg _ _)
  · exact le_rfl

private theorem tendsto_routeETerminalPrimeNormalizedError_of_mem
    {r κ : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1)
    (herror : ∀ ε > 0, ∀ᶠ X : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
        |t| ≤ Real.exp (κ * Real.sqrt (Real.log X)) →
        Real.log X ^ 3 / X ^ (1 - r) *
          |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤ ε)
    (t : ℝ → ℝ)
    (ht : ∀ᶠ L : ℝ in atTop,
      t L ∈ Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L)) :
    Tendsto (fun L : ℝ =>
      L ^ 3 / Real.exp ((1 - r) * L) *
        |routeETerminalPrimeFrame r (Real.exp L) (t L) -
          routeETerminalPrimeMain r (Real.exp L) (t L)|) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := herror (ε / 2) (by positivity)
  have heL : ∀ᶠ L : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ s : ℝ,
        |s| ≤ Real.exp (κ * Real.sqrt (Real.log (Real.exp L))) →
        Real.log (Real.exp L) ^ 3 / (Real.exp L) ^ (1 - r) *
          |routeETerminalPrimeFrame r (Real.exp L) s -
            routeETerminalPrimeMain r (Real.exp L) s| ≤ ε / 2 :=
    Real.tendsto_exp_atTop.eventually he
  filter_upwards [heL, ht, eventually_ge_atTop (0 : ℝ)] with L heL hmem hL0
  have htAbs : |t L| ≤ routeETerminalFrequencyRadius κ L :=
    abs_le.2 hmem
  have hbound := heL r hr (t L) (by
    simpa [routeETerminalFrequencyRadius] using htAbs)
  have hscale0 : 0 ≤ L ^ 3 / Real.exp ((1 - r) * L) := by
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (mul_nonneg hscale0 (abs_nonneg _))]
  have hpow : (Real.exp L) ^ (1 - r) =
      Real.exp ((1 - r) * L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
    congr 1
    ring
  simpa [hpow, Real.log_exp] using hbound.trans_lt (by linarith)

/-- Prime minimax transport from a uniform normalized PNT error estimate.  Keeping the
transport assumption explicit lets the same absolute window control both the minimum and its
frequency localization. -/
theorem tendsto_routeETerminalPrimeConstrainedMinimum_of_normalizedError
    {κ : ℝ} (hκ : 0 < κ)
    (herror : ∀ ε > 0, ∀ᶠ X : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
        |t| ≤ Real.exp (κ * Real.sqrt (Real.log X)) →
        Real.log X ^ 3 / X ^ (1 - r) *
          |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤ ε)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun L : ℝ =>
      L ^ 3 / Real.exp ((1 - r) * L) *
        routeETerminalPrimeConstrainedMinimum r κ L) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
  let tP : ℝ → ℝ := fun L =>
    routeETerminalPrimeConstrainedMinimizer r κ L
  let tC : ℝ → ℝ := fun L =>
    routeETerminalConstrainedMinimizer (1 - r) κ L
  have htPmem : ∀ᶠ L : ℝ in atTop,
      tP L ∈ Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L) :=
    Eventually.of_forall fun L => routeETerminalPrimeConstrainedMinimizer_mem r κ L
  have htCmem : ∀ᶠ L : ℝ in atTop,
      tC L ∈ Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L) :=
    Eventually.of_forall fun L => routeETerminalConstrainedMinimizer_mem (1 - r) κ L
  have herrP := tendsto_routeETerminalPrimeNormalizedError_of_mem hr herror tP htPmem
  have herrC := tendsto_routeETerminalPrimeNormalizedError_of_mem hr herror tC htCmem
  have ha0 : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
  have ha1 : 1 - r ≤ 1 := by linarith [hr.1]
  have hcont := tendsto_routeETerminalConstrainedMinimum
    (1 - r) κ ha0 ha1 hκ
  have hshift : Tendsto (fun L : ℝ => L - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) tendsto_id
  have hfactor : Tendsto (fun L : ℝ => L / (L - 1)) atTop (nhds 1) := by
    have hinv : Tendsto (fun L : ℝ => (L - 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hshift
    have hraw : Tendsto (fun L : ℝ => 1 + (L - 1)⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop (1 : ℝ)] with L hL
    field_simp [sub_ne_zero.mpr hL]
    ring
  have hupperMain := hfactor.mul hcont
  simp only [one_mul] at hupperMain
  let F : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - r) * L) *
      routeETerminalPrimeConstrainedMinimum r κ L
  let G : ℝ → ℝ := fun L =>
    L ^ 2 * routeETerminalConstrainedMinimum (1 - r) κ L
  let EP : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - r) * L) *
      |routeETerminalPrimeFrame r (Real.exp L) (tP L) -
        routeETerminalPrimeMain r (Real.exp L) (tP L)|
  let EC : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - r) * L) *
      |routeETerminalPrimeFrame r (Real.exp L) (tC L) -
        routeETerminalPrimeMain r (Real.exp L) (tC L)|
  have hlowLimit : Tendsto (fun L => G L - EP L) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
    simpa [G, EP] using hcont.sub herrP
  have huppLimit : Tendsto (fun L =>
      L / (L - 1) * G L + EC L) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
    simpa [G, EC] using hupperMain.add herrC
  have hbounds : ∀ᶠ L : ℝ in atTop,
      G L - EP L ≤ F L ∧ F L ≤ L / (L - 1) * G L + EC L := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    have hscale0 : 0 ≤ L ^ 3 / Real.exp ((1 - r) * L) := by positivity
    have hPmain := routeETerminalDenominatedEnergy_compare
      (a := 1 - r) (t := tP L) hL
    have hCmain := routeETerminalDenominatedEnergy_compare
      (a := 1 - r) (t := tC L) hL
    have hminP := routeETerminalConstrainedMinimum_le
      (1 - r) κ L (tP L) (routeETerminalPrimeConstrainedMinimizer_mem r κ L)
    have hminC := routeETerminalPrimeConstrainedMinimum_le
      r κ L (tC L) (routeETerminalConstrainedMinimizer_mem (1 - r) κ L)
    have hframeLower : routeETerminalPrimeMain r (Real.exp L) (tP L) -
        |routeETerminalPrimeFrame r (Real.exp L) (tP L) -
          routeETerminalPrimeMain r (Real.exp L) (tP L)| ≤
        routeETerminalPrimeConstrainedMinimum r κ L := by
      dsimp [tP, routeETerminalPrimeConstrainedMinimum]
      linarith [neg_le_abs (routeETerminalPrimeFrame r (Real.exp L)
        (routeETerminalPrimeConstrainedMinimizer r κ L) -
          routeETerminalPrimeMain r (Real.exp L)
            (routeETerminalPrimeConstrainedMinimizer r κ L))]
    have hframeUpper : routeETerminalPrimeConstrainedMinimum r κ L ≤
        routeETerminalPrimeMain r (Real.exp L) (tC L) +
          |routeETerminalPrimeFrame r (Real.exp L) (tC L) -
            routeETerminalPrimeMain r (Real.exp L) (tC L)| :=
      hminC.trans (by
        linarith [le_abs_self (routeETerminalPrimeFrame r (Real.exp L) (tC L) -
          routeETerminalPrimeMain r (Real.exp L) (tC L))])
    constructor
    · have hL0 : 0 < L := zero_lt_one.trans hL
      have hminDiv : routeETerminalConstrainedMinimum (1 - r) κ L / L ≤
          routeETerminalContinuousEnergy (1 - r) L (tP L) / L :=
        div_le_div_of_nonneg_right hminP hL0.le
      have hdenLower := hminDiv.trans hPmain.1
      have hnormMainLower := mul_le_mul_of_nonneg_left hdenLower
        (pow_nonneg hL0.le 3)
      have hmainScale :
          L ^ 3 / Real.exp ((1 - r) * L) *
              routeETerminalPrimeMain r (Real.exp L) (tP L) =
            L ^ 3 * routeETerminalDenominatedEnergy (1 - r) L (tP L) := by
        rw [routeETerminalPrimeMain_exp_eq_denominated]
        field_simp [Real.exp_ne_zero]
      have hGLower : G L ≤ L ^ 3 / Real.exp ((1 - r) * L) *
          routeETerminalPrimeMain r (Real.exp L) (tP L) := by
        calc
          G L = L ^ 3 *
              (routeETerminalConstrainedMinimum (1 - r) κ L / L) := by
            dsimp [G]
            field_simp [hL0.ne']
          _ ≤ L ^ 3 * routeETerminalDenominatedEnergy (1 - r) L (tP L) :=
            hnormMainLower
          _ = L ^ 3 / Real.exp ((1 - r) * L) *
              routeETerminalPrimeMain r (Real.exp L) (tP L) := hmainScale.symm
      have hs := mul_le_mul_of_nonneg_left hframeLower hscale0
      have hs' : L ^ 3 / Real.exp ((1 - r) * L) *
            routeETerminalPrimeMain r (Real.exp L) (tP L) - EP L ≤ F L := by
        dsimp [EP, F]
        linarith
      linarith
    · have hLm1 : 0 < L - 1 := sub_pos.mpr hL
      have hnormMainUpper := mul_le_mul_of_nonneg_left hCmain.2
        (pow_nonneg (zero_lt_one.trans hL).le 3)
      have hmainScale :
          L ^ 3 / Real.exp ((1 - r) * L) *
              routeETerminalPrimeMain r (Real.exp L) (tC L) =
            L ^ 3 * routeETerminalDenominatedEnergy (1 - r) L (tC L) := by
        rw [routeETerminalPrimeMain_exp_eq_denominated]
        field_simp [Real.exp_ne_zero]
      have hGUpper : L ^ 3 / Real.exp ((1 - r) * L) *
          routeETerminalPrimeMain r (Real.exp L) (tC L) ≤
            L / (L - 1) * G L := by
        calc
          L ^ 3 / Real.exp ((1 - r) * L) *
              routeETerminalPrimeMain r (Real.exp L) (tC L) =
              L ^ 3 * routeETerminalDenominatedEnergy (1 - r) L (tC L) :=
            hmainScale
          _ ≤ L ^ 3 *
              (routeETerminalContinuousEnergy (1 - r) L (tC L) / (L - 1)) :=
            hnormMainUpper
          _ = L / (L - 1) * G L := by
            dsimp [G, tC, routeETerminalConstrainedMinimum]
            field_simp [hLm1.ne']
      have hs := mul_le_mul_of_nonneg_left hframeUpper hscale0
      have hs' : F L ≤ L ^ 3 / Real.exp ((1 - r) * L) *
            routeETerminalPrimeMain r (Real.exp L) (tC L) + EC L := by
        dsimp [F, EC]
        linarith
      linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowLimit huppLimit
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- **Literal prime theorem `(3)`.** One absolute positive PNT-controlled subexponential
window works simultaneously for every fixed `0 < r ≤ 1`; on it, compact-window moving-prime
minima have exact sharp variance constant. -/
theorem exists_kappa_tendsto_routeETerminalPrimeConstrainedMinimum :
    ∃ κ > 0, ∀ r ∈ Ioc (0 : ℝ) 1,
      Tendsto (fun L : ℝ =>
        L ^ 3 / Real.exp ((1 - r) * L) *
          routeETerminalPrimeConstrainedMinimum r κ L) atTop
        (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
  obtain ⟨κ, hκ, herror⟩ :=
    exists_routeETerminalPrimeFrame_normalizedError_uniform_subexp
  exact ⟨κ, hκ, fun r hr =>
    tendsto_routeETerminalPrimeConstrainedMinimum_of_normalizedError
      hκ herror r hr⟩

/-- A literal-prime minimizer has continuous normalized energy equal to the sharp variance
constant.  Thus prime discreteness and the logarithmic denominator cannot create an optimizer
escape mode inside the PNT window. -/
theorem tendsto_routeETerminalContinuousEnergy_at_primeConstrainedMinimizer_of_normalizedError
    {κ : ℝ} (hκ : 0 < κ)
    (herror : ∀ ε > 0, ∀ᶠ X : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
        |t| ≤ Real.exp (κ * Real.sqrt (Real.log X)) →
        Real.log X ^ 3 / X ^ (1 - r) *
          |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤ ε)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun L : ℝ => L ^ 2 *
      routeETerminalContinuousEnergy (1 - r) L
        (routeETerminalPrimeConstrainedMinimizer r κ L)) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
  let tP : ℝ → ℝ := fun L =>
    routeETerminalPrimeConstrainedMinimizer r κ L
  let F : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - r) * L) *
      routeETerminalPrimeConstrainedMinimum r κ L
  let PM : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - r) * L) *
      routeETerminalPrimeMain r (Real.exp L) (tP L)
  let EP : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - r) * L) *
      |routeETerminalPrimeFrame r (Real.exp L) (tP L) -
        routeETerminalPrimeMain r (Real.exp L) (tP L)|
  let G : ℝ → ℝ := fun L =>
    L ^ 2 * routeETerminalContinuousEnergy (1 - r) L (tP L)
  have htPmem : ∀ᶠ L : ℝ in atTop,
      tP L ∈ Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L) :=
    Eventually.of_forall fun L => routeETerminalPrimeConstrainedMinimizer_mem r κ L
  have herr := tendsto_routeETerminalPrimeNormalizedError_of_mem
    hr herror tP htPmem
  have hprime :=
    tendsto_routeETerminalPrimeConstrainedMinimum_of_normalizedError
      hκ herror r hr
  have hPMLower : Tendsto (fun L => F L - EP L) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
    simpa [F, EP] using hprime.sub herr
  have hPMUpper : Tendsto (fun L => F L + EP L) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
    simpa [F, EP] using hprime.add herr
  have hPMBounds : ∀ᶠ L : ℝ in atTop,
      F L - EP L ≤ PM L ∧ PM L ≤ F L + EP L := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL0
    have hscale0 : 0 ≤ L ^ 3 / Real.exp ((1 - r) * L) := by positivity
    have hleftRaw :
        routeETerminalPrimeFrame r (Real.exp L) (tP L) -
            |routeETerminalPrimeFrame r (Real.exp L) (tP L) -
              routeETerminalPrimeMain r (Real.exp L) (tP L)| ≤
          routeETerminalPrimeMain r (Real.exp L) (tP L) := by
      linarith [le_abs_self (routeETerminalPrimeFrame r (Real.exp L) (tP L) -
        routeETerminalPrimeMain r (Real.exp L) (tP L))]
    have hrightRaw :
        routeETerminalPrimeMain r (Real.exp L) (tP L) ≤
          routeETerminalPrimeFrame r (Real.exp L) (tP L) +
            |routeETerminalPrimeFrame r (Real.exp L) (tP L) -
              routeETerminalPrimeMain r (Real.exp L) (tP L)| := by
      linarith [neg_le_abs (routeETerminalPrimeFrame r (Real.exp L) (tP L) -
        routeETerminalPrimeMain r (Real.exp L) (tP L))]
    have hleft := mul_le_mul_of_nonneg_left hleftRaw hscale0
    have hright := mul_le_mul_of_nonneg_left hrightRaw hscale0
    constructor
    · dsimp [F, PM, EP, routeETerminalPrimeConstrainedMinimum]
      simpa [mul_sub] using hleft
    · dsimp [F, PM, EP, routeETerminalPrimeConstrainedMinimum]
      simpa [mul_add] using hright
  have hPM : Tendsto PM atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hPMLower hPMUpper
      (hPMBounds.mono fun _ h => h.1) (hPMBounds.mono fun _ h => h.2)
  have hbackFactor : Tendsto (fun L : ℝ => (L - 1) / L) atTop (nhds 1) := by
    have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hraw : Tendsto (fun L : ℝ => 1 - L⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hinv
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
    field_simp [hL]
  have hGLower : Tendsto (fun L => (L - 1) / L * PM L) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
    simpa using hbackFactor.mul hPM
  have hGBounds : ∀ᶠ L : ℝ in atTop,
      (L - 1) / L * PM L ≤ G L ∧ G L ≤ PM L := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    have hL0 : 0 < L := zero_lt_one.trans hL
    have hLm1 : 0 < L - 1 := sub_pos.mpr hL
    have hcomp := routeETerminalDenominatedEnergy_compare
      (a := 1 - r) (t := tP L) hL
    have hcube : 0 ≤ L ^ 3 := (pow_pos hL0 3).le
    have hmainScale : PM L = L ^ 3 *
        routeETerminalDenominatedEnergy (1 - r) L (tP L) := by
      dsimp [PM]
      rw [routeETerminalPrimeMain_exp_eq_denominated]
      field_simp [Real.exp_ne_zero]
    have hGlePM : G L ≤ PM L := by
      calc
        G L = L ^ 3 *
            (routeETerminalContinuousEnergy (1 - r) L (tP L) / L) := by
          dsimp [G]
          field_simp [hL0.ne']
        _ ≤ L ^ 3 * routeETerminalDenominatedEnergy (1 - r) L (tP L) :=
          mul_le_mul_of_nonneg_left hcomp.1 hcube
        _ = PM L := hmainScale.symm
    have hPMle : PM L ≤ L / (L - 1) * G L := by
      calc
        PM L = L ^ 3 *
            routeETerminalDenominatedEnergy (1 - r) L (tP L) := hmainScale
        _ ≤ L ^ 3 *
            (routeETerminalContinuousEnergy (1 - r) L (tP L) / (L - 1)) :=
          mul_le_mul_of_nonneg_left hcomp.2 hcube
        _ = L / (L - 1) * G L := by
          dsimp [G]
          field_simp [hLm1.ne', hL0.ne']
    constructor
    · have hfactor0 : 0 ≤ (L - 1) / L := div_nonneg hLm1.le hL0.le
      have hs := mul_le_mul_of_nonneg_left hPMle hfactor0
      calc
        (L - 1) / L * PM L ≤
            (L - 1) / L * (L / (L - 1) * G L) := hs
        _ = G L := by field_simp [hLm1.ne', hL0.ne']
    · exact hGlePM
  have hG : Tendsto G atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hGLower hPM
      (hGBounds.mono fun _ h => h.1) (hGBounds.mono fun _ h => h.2)
  simpa [G, tP] using hG

/-- **Literal prime optimizer theorem `(5)`.** Every sequence of genuine compact-window prime
minimizers admits a sign subsequence with first odd phase `±π` and the unique terminal-mean
second-order correction. -/
theorem routeETerminalPrimeConstrainedMinimizer_sign_subsequence_of_normalizedError
    {κ : ℝ} (hκ : 0 < κ)
    (herror : ∀ ε > 0, ∀ᶠ X : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
        |t| ≤ Real.exp (κ * Real.sqrt (Real.log X)) →
        Real.log X ^ 3 / X ^ (1 - r) *
          |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤ ε)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    ∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
      ((Tendsto (fun n =>
          routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n))
          atTop (nhds Real.pi) ∧
        Tendsto (fun n => R (χ n) *
          (routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n) -
            Real.pi)) atTop
          (nhds (Real.pi * routeETerminalMean (1 - r)))) ∨
       (Tendsto (fun n =>
          routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n))
          atTop (nhds (-Real.pi)) ∧
        Tendsto (fun n => R (χ n) *
          (routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n) -
            (-Real.pi))) atTop
          (nhds ((-Real.pi) * routeETerminalMean (1 - r))))) := by
  have ha0 : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
  have ha1 : 1 - r ≤ 1 := by linarith [hr.1]
  have henergyReal :=
    tendsto_routeETerminalContinuousEnergy_at_primeConstrainedMinimizer_of_normalizedError
      hκ herror r hr
  have henergyNat : Tendsto (fun n => R n ^ 2 *
      routeETerminalContinuousEnergy (1 - r) (R n)
        (routeETerminalPrimeConstrainedMinimizer r κ (R n))) atTop
      (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) := by
    simpa [Function.comp_def] using henergyReal.comp hR
  exact routeETerminal_asymptoticMinimizer_sign_subsequence
    (1 - r) ha0 ha1 R
      (fun n => routeETerminalPrimeConstrainedMinimizer r κ (R n)) hR henergyNat

/-- One absolute prime window simultaneously realizes the sharp minimum `(3)` and the complete
sign-subsequence localization `(5)` for every `0 < r ≤ 1`. -/
theorem exists_kappa_routeETerminalPrime_minimum_and_optimizer :
    ∃ κ > 0, ∀ r ∈ Ioc (0 : ℝ) 1,
      Tendsto (fun L : ℝ =>
        L ^ 3 / Real.exp ((1 - r) * L) *
          routeETerminalPrimeConstrainedMinimum r κ L) atTop
        (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - r))) ∧
      ∀ R : ℕ → ℝ, Tendsto R atTop atTop →
        ∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
          ((Tendsto (fun n =>
              routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n))
              atTop (nhds Real.pi) ∧
            Tendsto (fun n => R (χ n) *
              (routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n) -
                Real.pi)) atTop
              (nhds (Real.pi * routeETerminalMean (1 - r)))) ∨
           (Tendsto (fun n =>
              routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n))
              atTop (nhds (-Real.pi)) ∧
            Tendsto (fun n => R (χ n) *
              (routeETerminalPrimeConstrainedMinimizer r κ (R (χ n)) * R (χ n) -
                (-Real.pi))) atTop
              (nhds ((-Real.pi) * routeETerminalMean (1 - r))))) := by
  obtain ⟨κ, hκ, herror⟩ :=
    exists_routeETerminalPrimeFrame_normalizedError_uniform_subexp
  refine ⟨κ, hκ, ?_⟩
  intro r hr
  exact ⟨tendsto_routeETerminalPrimeConstrainedMinimum_of_normalizedError
      hκ herror r hr,
    fun R hR =>
      routeETerminalPrimeConstrainedMinimizer_sign_subsequence_of_normalizedError
        hκ herror r hr R hR⟩

/-! ## Literal all-order source histories -/

/-- Literal terminal prime frame after applying the canonical source damping at arbitrary real
order `q`. Finite-volume prime support and phase history are unchanged. -/
def routeETerminalSourceFrame (q X t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊X / Real.exp 1⌋₊ ⌊X⌋₊,
    if hp : k.Prime then
      xiMobiusPrimeSchurValuationDamping ⟨k, hp⟩ ^ q *
        routeETerminalPhaseEnergy t k
    else 0

theorem routeETerminalSourceFrame_nonneg
    {q X t : ℝ} (_hq0 : 0 < q) :
    0 ≤ routeETerminalSourceFrame q X t := by
  rw [routeETerminalSourceFrame]
  apply Finset.sum_nonneg
  intro k hk
  split_ifs with hp
  · have hd : 0 ≤ xiMobiusPrimeSchurValuationDamping (⟨k, hp⟩ : Nat.Primes) := by
      rw [xiMobiusPrimeSchurValuationDamping_eq_prime_rpow]
      positivity
    exact mul_nonneg (Real.rpow_nonneg hd _)
      (routeETerminalPhaseEnergy_nonneg _ _)
  · exact le_rfl

theorem continuous_routeETerminalSourceFrame_frequency (q X : ℝ) :
    Continuous (fun t => routeETerminalSourceFrame q X t) := by
  unfold routeETerminalSourceFrame
  refine continuous_finsetSum _ fun k hk => ?_
  by_cases hp : k.Prime
  · simp only [hp, dite_true]
    unfold routeETerminalPhaseEnergy
    fun_prop
  · simp only [hp, dite_false]
    exact continuous_const

/-- Prime-dilation geometry turns the pointwise likelihood defect into a relative `3e/X`
defect. This retains every phase value and is stronger than summing a separate prime-counting
majorant. -/
theorem routeETerminalPrimeFrame_sub_sourceFrame_nonneg_le
    {q X t : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2) (hX : 0 < X) :
    0 ≤ routeETerminalPrimeFrame (q / 2) X t -
        routeETerminalSourceFrame q X t ∧
      routeETerminalPrimeFrame (q / 2) X t -
        routeETerminalSourceFrame q X t ≤
          (3 * Real.exp 1 / X) * routeETerminalPrimeFrame (q / 2) X t := by
  let S := Finset.Ioc ⌊X / Real.exp 1⌋₊ ⌊X⌋₊
  have hpointNonneg : ∀ k ∈ S,
      0 ≤ (if hp : k.Prime then
        (k : ℝ) ^ (-(q / 2)) * routeETerminalPhaseEnergy t k else 0) -
        (if hp : k.Prime then
          xiMobiusPrimeSchurValuationDamping ⟨k, hp⟩ ^ q *
            routeETerminalPhaseEnergy t k else 0) := by
    intro k hk
    by_cases hp : k.Prime
    · simp only [hp, dite_true]
      have hneg : -(q / 2) = -q / 2 := by ring
      have hdef := (xiMobiusPrimeSchurValuationDamping_rpow_defect
        (⟨k, hp⟩ : Nat.Primes) hq0 hq2).1
      have hmul := mul_nonneg hdef (routeETerminalPhaseEnergy_nonneg t k)
      simpa [hneg, sub_mul] using hmul
    · simp only [hp, dite_false]
      norm_num
  have hpointUpper : ∀ k ∈ S,
      (if hp : k.Prime then
        (k : ℝ) ^ (-(q / 2)) * routeETerminalPhaseEnergy t k else 0) -
        (if hp : k.Prime then
          xiMobiusPrimeSchurValuationDamping ⟨k, hp⟩ ^ q *
            routeETerminalPhaseEnergy t k else 0) ≤
      (3 * Real.exp 1 / X) *
        (if hp : k.Prime then
          (k : ℝ) ^ (-(q / 2)) * routeETerminalPhaseEnergy t k else 0) := by
    intro k hk
    by_cases hp : k.Prime
    · simp only [hp, dite_true]
      have hneg : -(q / 2) = -q / 2 := by ring
      let p : Nat.Primes := ⟨k, hp⟩
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast hp.pos
      have hfloor : ⌊X / Real.exp 1⌋₊ < k := (Finset.mem_Ioc.mp hk).1
      have hsucc : ⌊X / Real.exp 1⌋₊ + 1 ≤ k := by omega
      have hlow : X / Real.exp 1 < (k : ℝ) :=
        lt_of_lt_of_le (Nat.lt_floor_add_one (X / Real.exp 1))
          (by exact_mod_cast hsucc)
      have hXlt : X < (k : ℝ) * Real.exp 1 :=
        (div_lt_iff₀ (Real.exp_pos 1)).mp hlow
      have hXdiv : X / (k : ℝ) < Real.exp 1 :=
        (div_lt_iff₀ hkpos).2 (by simpa [mul_comm] using hXlt)
      have hinv : (k : ℝ)⁻¹ ≤ Real.exp 1 / X := by
        rw [le_div_iff₀ hX]
        rw [show (k : ℝ)⁻¹ * X = X / (k : ℝ) by ring]
        exact hXdiv.le
      have hdef :=
        (xiMobiusPrimeSchurValuationDamping_rpow_defect p hq0 hq2).2
      have hphase0 := routeETerminalPhaseEnergy_nonneg t k
      have hmul := mul_le_mul_of_nonneg_right hdef hphase0
      have hpow0 : 0 ≤ (k : ℝ) ^ (-q / 2) := by positivity
      have hrel : 3 * (k : ℝ) ^ (-q / 2 - 1) *
          routeETerminalPhaseEnergy t k ≤
          (3 * Real.exp 1 / X) *
            ((k : ℝ) ^ (-q / 2) * routeETerminalPhaseEnergy t k) := by
        rw [show -q / 2 - 1 = -q / 2 + (-1 : ℝ) by ring,
          Real.rpow_add hkpos, Real.rpow_neg_one]
        have hm := mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hpow0) hphase0)
        calc
          3 * ((k : ℝ) ^ (-q / 2) * (k : ℝ)⁻¹) *
              routeETerminalPhaseEnergy t k =
              (3 * (k : ℝ) ^ (-q / 2) *
                routeETerminalPhaseEnergy t k) * (k : ℝ)⁻¹ := by ring
          _ ≤ (3 * (k : ℝ) ^ (-q / 2) *
                routeETerminalPhaseEnergy t k) * (Real.exp 1 / X) := hm
          _ = (3 * Real.exp 1 / X) *
              ((k : ℝ) ^ (-q / 2) * routeETerminalPhaseEnergy t k) := by ring
      simpa [p, hneg, sub_mul] using hmul.trans hrel
    · simp only [hp, dite_false]
      norm_num
  rw [routeETerminalPrimeFrame, routeETerminalSourceFrame]
  change 0 ≤ (∑ k ∈ S, _) - ∑ k ∈ S, _ ∧
    (∑ k ∈ S, _) - ∑ k ∈ S, _ ≤ _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact ⟨Finset.sum_nonneg hpointNonneg, Finset.sum_le_sum hpointUpper⟩

noncomputable def routeETerminalSourceConstrainedMinimizer
    (q κ L : ℝ) : ℝ :=
  Classical.choose (by
    have hne : (Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L)).Nonempty :=
      nonempty_Icc.mpr (by linarith [routeETerminalFrequencyRadius_pos κ L])
    exact isCompact_Icc.exists_isMinOn hne
      (continuous_routeETerminalSourceFrame_frequency q (Real.exp L)).continuousOn)

noncomputable def routeETerminalSourceConstrainedMinimum
    (q κ L : ℝ) : ℝ :=
  routeETerminalSourceFrame q (Real.exp L)
    (routeETerminalSourceConstrainedMinimizer q κ L)

theorem routeETerminalSourceConstrainedMinimizer_mem (q κ L : ℝ) :
    routeETerminalSourceConstrainedMinimizer q κ L ∈
      Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L) := by
  exact (Classical.choose_spec (show ∃ t ∈
      Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L),
      IsMinOn (fun s => routeETerminalSourceFrame q (Real.exp L) s)
        (Icc (-routeETerminalFrequencyRadius κ L)
          (routeETerminalFrequencyRadius κ L)) t from by
    have hne : (Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L)).Nonempty :=
      nonempty_Icc.mpr (by linarith [routeETerminalFrequencyRadius_pos κ L])
    exact isCompact_Icc.exists_isMinOn hne
      (continuous_routeETerminalSourceFrame_frequency q (Real.exp L)).continuousOn)).1

theorem routeETerminalSourceConstrainedMinimum_le
    (q κ L t : ℝ)
    (ht : t ∈ Icc (-routeETerminalFrequencyRadius κ L)
      (routeETerminalFrequencyRadius κ L)) :
    routeETerminalSourceConstrainedMinimum q κ L ≤
      routeETerminalSourceFrame q (Real.exp L) t := by
  exact (isMinOn_iff.mp (Classical.choose_spec (show ∃ s ∈
      Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L),
      IsMinOn (fun u => routeETerminalSourceFrame q (Real.exp L) u)
        (Icc (-routeETerminalFrequencyRadius κ L)
          (routeETerminalFrequencyRadius κ L)) s from by
    have hne : (Icc (-routeETerminalFrequencyRadius κ L)
        (routeETerminalFrequencyRadius κ L)).Nonempty :=
      nonempty_Icc.mpr (by linarith [routeETerminalFrequencyRadius_pos κ L])
    exact isCompact_Icc.exists_isMinOn hne
      (continuous_routeETerminalSourceFrame_frequency q (Real.exp L)).continuousOn)).2) t ht

/-- **All-order source theorem `(9)`.** The same absolute PNT window works at every source order
`0 < q ≤ 2`; canonical likelihood damping leaves exact terminal minimax constant unchanged. -/
theorem exists_kappa_tendsto_routeETerminalSourceConstrainedMinimum :
    ∃ κ > 0, ∀ q ∈ Ioc (0 : ℝ) 2,
      Tendsto (fun L : ℝ =>
        L ^ 3 / Real.exp ((1 - q / 2) * L) *
          routeETerminalSourceConstrainedMinimum q κ L) atTop
        (nhds (Real.pi ^ 2 * routeETerminalVariance (1 - q / 2))) := by
  obtain ⟨κ, hκ, hprime⟩ :=
    exists_kappa_tendsto_routeETerminalPrimeConstrainedMinimum
  refine ⟨κ, hκ, ?_⟩
  intro q hq
  have hr : q / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hp := hprime (q / 2) hr
  have hfactor : Tendsto (fun L : ℝ =>
      1 - 3 * Real.exp 1 / Real.exp L) atTop (nhds 1) := by
    have hinv : Tendsto (fun L : ℝ => (Real.exp L)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop
    have hterm := hinv.const_mul (3 * Real.exp 1)
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hterm
  have hlowerLimit := hfactor.mul hp
  simp only [one_mul] at hlowerLimit
  let FS : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - q / 2) * L) *
      routeETerminalSourceConstrainedMinimum q κ L
  let FP : ℝ → ℝ := fun L =>
    L ^ 3 / Real.exp ((1 - q / 2) * L) *
      routeETerminalPrimeConstrainedMinimum (q / 2) κ L
  have hbounds : ∀ᶠ L : ℝ in atTop,
      (1 - 3 * Real.exp 1 / Real.exp L) * FP L ≤ FS L ∧
        FS L ≤ FP L := by
    filter_upwards [eventually_ge_atTop (Real.log (3 * Real.exp 1)),
      eventually_ge_atTop (0 : ℝ)] with L hL hL0
    have hfac0 : 0 ≤ 1 - 3 * Real.exp 1 / Real.exp L := by
      rw [sub_nonneg, div_le_one (Real.exp_pos L)]
      have := Real.exp_le_exp.mpr hL
      simpa [Real.exp_log (by positivity : 0 < 3 * Real.exp 1)] using this
    let tS := routeETerminalSourceConstrainedMinimizer q κ L
    let tP := routeETerminalPrimeConstrainedMinimizer (q / 2) κ L
    have hcompS := routeETerminalPrimeFrame_sub_sourceFrame_nonneg_le
      hq.1 hq.2 (Real.exp_pos L) (t := tS)
    have hcompP := routeETerminalPrimeFrame_sub_sourceFrame_nonneg_le
      hq.1 hq.2 (Real.exp_pos L) (t := tP)
    have hprimeMinAtS := routeETerminalPrimeConstrainedMinimum_le
      (q / 2) κ L tS (routeETerminalSourceConstrainedMinimizer_mem q κ L)
    have hsourceMinAtP := routeETerminalSourceConstrainedMinimum_le
      q κ L tP (routeETerminalPrimeConstrainedMinimizer_mem (q / 2) κ L)
    have hlowerRaw : (1 - 3 * Real.exp 1 / Real.exp L) *
        routeETerminalPrimeConstrainedMinimum (q / 2) κ L ≤
          routeETerminalSourceConstrainedMinimum q κ L := by
      have hsourceAtS : (1 - 3 * Real.exp 1 / Real.exp L) *
          routeETerminalPrimeFrame (q / 2) (Real.exp L) tS ≤
            routeETerminalSourceFrame q (Real.exp L) tS := by
        dsimp [tS]
        linarith
      exact (mul_le_mul_of_nonneg_left hprimeMinAtS hfac0).trans hsourceAtS
    have hupperRaw : routeETerminalSourceConstrainedMinimum q κ L ≤
        routeETerminalPrimeConstrainedMinimum (q / 2) κ L := by
      calc
        routeETerminalSourceConstrainedMinimum q κ L ≤
            routeETerminalSourceFrame q (Real.exp L) tP := hsourceMinAtP
        _ ≤ routeETerminalPrimeFrame (q / 2) (Real.exp L) tP := by
          linarith [hcompP.1]
        _ = routeETerminalPrimeConstrainedMinimum (q / 2) κ L := by
          rfl
    have hscale0 : 0 ≤ L ^ 3 / Real.exp ((1 - q / 2) * L) := by
      positivity
    constructor
    · dsimp [FP, FS]
      have := mul_le_mul_of_nonneg_left hlowerRaw hscale0
      nlinarith
    · exact mul_le_mul_of_nonneg_left hupperRaw hscale0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa [FP] using hlowerLimit) (by simpa [FP] using hp)
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- Physical half-density and Fisher endpoints of the all-order source law. -/
theorem exists_kappa_routeETerminalSource_endpoints :
    ∃ κ > 0,
      Tendsto (fun L : ℝ =>
        L ^ 3 / Real.exp ((1 / 2 : ℝ) * L) *
          routeETerminalSourceConstrainedMinimum 1 κ L) atTop
        (nhds (Real.pi ^ 2 * routeETerminalVariance (1 / 2))) ∧
      Tendsto (fun L : ℝ =>
        L ^ 3 * routeETerminalSourceConstrainedMinimum 2 κ L) atTop
        (nhds (Real.pi ^ 2 / 12)) := by
  obtain ⟨κ, hκ, hsource⟩ :=
    exists_kappa_tendsto_routeETerminalSourceConstrainedMinimum
  refine ⟨κ, hκ, ?_, ?_⟩
  · convert hsource 1 (by constructor <;> norm_num) using 1
    · funext L
      ring
    · ring
  · have h := hsource 2 (by constructor <;> norm_num)
    have h' : Tendsto (fun L : ℝ =>
        L ^ 3 * routeETerminalSourceConstrainedMinimum 2 κ L) atTop
          (nhds (Real.pi ^ 2 * (1 / 12 : ℝ))) := by
      simpa only [show (1 - (2 : ℝ) / 2) = 0 by norm_num,
        zero_mul, Real.exp_zero, div_one, routeETerminalVariance_zero]
        using h
    convert h' using 1
    ring

end
end RHTower
