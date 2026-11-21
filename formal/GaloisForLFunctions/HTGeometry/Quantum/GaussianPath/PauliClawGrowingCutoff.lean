import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliClawProbability
import GaloisForLFunctions.HTGeometry.GaussianQuotientFusionCapital
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PairedRows
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A growing coefficient cutoff for the Gaussian Pauli claw

A six-coordinate block survives just below the scale sqrt(log(n+1)/3),
where n+2 is the number of sites. Gaussian lower bounds on a fixed
interval beyond the cutoff make the finite-prefix failure probabilities
summable. The obstruction therefore holds eventually on a common draw.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The scale at which the product of six Gaussian tails has leading inverse-prefix size. -/
def clawCutoffScale (n : ℕ) : ℝ := Real.sqrt (Real.log ((n : ℝ) + 1) / 3)

theorem clawCutoffScale_sq (n : ℕ) :
    clawCutoffScale n ^ 2 = Real.log ((n : ℝ) + 1) / 3 := by
  have h : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact Real.sq_sqrt (div_nonneg (Real.log_nonneg h) (by positivity))

private theorem eventually_le_clawCutoffScale {r : ℝ} (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in atTop, r ≤ clawCutoffScale n := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_atTop.1 (Real.tendsto_log_atTop.comp hnat)) (3 * r ^ 2)] with n hn
  change 3 * r ^ 2 ≤ Real.log ((n : ℝ) + 1) at hn
  exact (Real.sqrt_sq hr).symm.trans_le (Real.sqrt_le_sqrt (by linarith only [hn]))

/-- A positive interval strictly beyond the cutoff gives a lower bound
with arbitrary fixed width. -/
theorem gaussianAbsoluteTailMass_interval_lower {t w : ℝ} (ht : 0 ≤ t) (hw : 0 < w) :
    ENNReal.ofReal (w / Real.sqrt (2 * Real.pi) * Real.exp (-((t + 2 * w) ^ 2 / 2))) ≤
      gaussianAbsoluteTailMass t := by
  let I := Icc (t + w) (t + 2 * w)
  let c := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((t + 2 * w) ^ 2 / 2))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd (x : ℝ) (hx : x ∈ I) : ENNReal.ofReal c ≤ gaussianPDF 0 1 x := by
    have hx₀ : 0 ≤ x := (add_nonneg ht hw.le).trans hx.1
    have hxs : x ^ 2 ≤ (t + 2 * w) ^ 2 :=
      (sq_le_sq₀ hx₀ (hx₀.trans hx.2)).mpr hx.2
    rw [gaussianPDF, gaussianPDFReal_def]
    apply ENNReal.ofReal_le_ofReal
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hxs])) (by positivity)
  have hsubset : I ⊆ {x : ℝ | t < |x|} := fun x hx =>
    (lt_add_of_pos_right t hw).trans_le (hx.1.trans (le_abs_self x))
  have hlen : (t + 2 * w) - (t + w) = w := by ring
  calc
    _ = ∫⁻ _ in I, ENNReal.ofReal c := by
      rw [setLIntegral_const, show volume I = ENNReal.ofReal w by
        dsimp [I]; rw [Real.volume_Icc, hlen], ← ENNReal.ofReal_mul hc]
      congr 1
      dsimp [c]
      ring
    _ ≤ ∫⁻ x in I, gaussianPDF 0 1 x :=
      setLIntegral_mono (by fun_prop) hd
    _ = gaussianReal 0 1 I := (gaussianReal_apply 0 one_ne_zero _).symm
    _ ≤ _ := measure_mono hsubset

private theorem failure_power_le_exp (q : ENNReal) (hq : q ≤ 1) (m : ℕ) :
    (1 - q) ^ m ≤ ENNReal.ofReal (Real.exp (-(q.toReal * (m : ℝ)))) := by
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  have hqreal : q.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq
  have hsub : 1 - q = ENNReal.ofReal (1 - q.toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hqtop, ENNReal.ofReal_one]
  rw [hsub, ← ENNReal.ofReal_pow (sub_nonneg.mpr hqreal)]
  apply ENNReal.ofReal_le_ofReal
  have he : 1 - q.toReal ≤ Real.exp (-q.toReal) := by
    linarith only [Real.add_one_le_exp (-q.toReal)]
  calc
    _ ≤ (Real.exp (-q.toReal)) ^ m := pow_le_pow_left₀ (sub_nonneg.mpr hqreal) he _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

private theorem eventually_claw_failure_le_inv_square {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      pathPauliDisorderLaw (noClawBlockEvent (clawCutoffScale n - ε) ((n + 1) / 2)) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by
  let w := ε / 4
  let a := ε / 2
  let c := w / Real.sqrt (2 * Real.pi)
  let K := c ^ 6 * Real.exp (-(3 * a ^ 2))
  let B := (K / 3) * (6 * a) ^ 3 / 6
  have hw : 0 < w := by dsimp [w]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := div_pos hw (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hreq : 0 ≤ max ε (6 / B) := hε.le.trans (le_max_left _ _)
  filter_upwards [eventually_le_clawCutoffScale hreq,
    eventually_ge_atTop (1 : ℕ)] with n hscale hn
  let r := clawCutoffScale n
  let N := (n : ℝ) + 1
  let m := (n + 1) / 2
  let q := gaussianAbsoluteTailMass (r - ε) ^ 6
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hεr : ε ≤ r := (le_max_left _ _).trans hscale
  have hBr : 6 / B ≤ r := (le_max_right _ _).trans hscale
  have hN : 0 < N := by dsimp [N]; positivity
  have hrlog : 3 * r ^ 2 = Real.log N := by
    rw [show r ^ 2 = Real.log N / 3 from clawCutoffScale_sq n]
    ring
  have hptail := gaussianAbsoluteTailMass_interval_lower (sub_nonneg.mpr hεr) hw
  have hqtail : ENNReal.ofReal (K * Real.exp (6 * a * r) / N) ≤ q := by
    have he : (c * Real.exp (-((r - ε + 2 * w) ^ 2 / 2))) ^ 6 =
        K * Real.exp (6 * a * r) / N := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have harg : ((6 : ℕ) : ℝ) * -((r - ε + 2 * w) ^ 2 / 2) =
          -(3 * a ^ 2) + 6 * a * r - Real.log N := by
        rw [← hrlog]
        dsimp [a, w]
        ring
      rw [harg, Real.exp_sub, Real.exp_add, Real.exp_log hN]
      dsimp [K]
      ring
    rw [← he, ENNReal.ofReal_pow (by positivity)]
    exact pow_le_pow_left' hptail 6
  have hq₁ : q ≤ 1 := by
    have hp : gaussianAbsoluteTailMass (r - ε) ≤ 1 := by
      unfold gaussianAbsoluteTailMass
      calc
        _ ≤ gaussianReal 0 1 Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact pow_le_one₀ zero_le hp
  have hqt : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq₁
  have hx := (ENNReal.ofReal_le_iff_le_toReal hqt).mp hqtail
  have hN_m : N ≤ 3 * (m : ℝ) := by
    have hh : n + 1 ≤ 3 * m := by dsimp [m]; omega
    change (n : ℝ) + 1 ≤ 3 * (m : ℝ)
    exact_mod_cast hh
  have hexp_le : (K / 3) * Real.exp (6 * a * r) ≤ q.toReal * (m : ℝ) := by
    have h := (div_le_iff₀ hN).mp hx
    have h' := mul_le_mul_of_nonneg_left hN_m (ENNReal.toReal_nonneg (a := q))
    nlinarith only [h, h']
  have hpoly : B * r ^ 3 ≤ (K / 3) * Real.exp (6 * a * r) := by
    have h := Real.pow_div_factorial_le_exp (6 * a * r) (show 0 ≤ 6 * a * r by positivity) 3
    have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf] at h
    calc
      _ = (K / 3) * ((6 * a * r) ^ 3 / 6) := by dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have hlarge : 2 * Real.log N ≤ q.toReal * (m : ℝ) := by
    have hrB : 6 ≤ B * r := by simpa only [mul_comm] using (div_le_iff₀ hB).mp hBr
    have h := mul_le_mul_of_nonneg_right hrB (sq_nonneg r)
    have h' : 2 * Real.log N ≤ B * r ^ 3 := by rw [← hrlog]; nlinarith only [h]
    exact h'.trans (hpoly.trans hexp_le)
  change pathPauliDisorderLaw (noClawBlockEvent (r - ε) m) ≤ ENNReal.ofReal (1 / N ^ 2)
  rw [gaussian_measure_noClawBlockEvent]
  refine (failure_power_le_exp q hq₁ m).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ Real.exp (-(2 * Real.log N)) := Real.exp_le_exp.mpr (neg_le_neg hlarge)
    _ = _ := by
      have he : Real.exp (2 * Real.log N) = N ^ 2 := by
        simpa only [Nat.cast_ofNat, Real.exp_log hN] using Real.exp_nat_mul (Real.log N) 2
      rw [Real.exp_neg, he, one_div]

/-- Almost surely a six-coordinate block survives eventually at any fixed
positive margin below the growing cutoff. -/
theorem gaussian_ae_eventually_clawBlock_at_growing_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∃ j ∈ Finset.range ((n + 1) / 2), pathPauliBlock ω j ∈ clawBlockEvent (clawCutoffScale n - ε) := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp (eventually_claw_failure_le_inv_square hε)
  let E (n : ℕ) := noClawBlockEvent (clawCutoffScale (k + n) - ε) ((k + n + 1) / 2)
  have hs : Summable (fun n : ℕ => 1 / ((↑(k + n) : ℝ) + 1) ^ 2) := by
    have h := Real.summable_one_div_nat_pow.mpr (show 1 < 2 by omega)
    simpa only [Function.comp_def, Nat.cast_succ] using
      h.comp_injective (show Function.Injective (fun n : ℕ => (k + n).succ) from
        fun _ _ he => Nat.add_left_cancel (Nat.succ.inj he))
  have hE : (∑' n, pathPauliDisorderLaw (E n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
    exact ENNReal.tsum_le_tsum fun n => hk (k + n) (Nat.le_add_right _ _)
  filter_upwards [ae_eventually_notMem hE] with ω hω
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hω
  refine eventually_atTop.mpr ⟨k + j₀, fun n hn => ?_⟩
  have hshift : j₀ ≤ n - k := by omega
  have he : k + (n - k) = n := by omega
  have hnE : ω ∉ noClawBlockEvent (clawCutoffScale n - ε) ((n + 1) / 2) := by
    simpa only [E, he] using hj₀ (n - k) hshift
  by_contra! hnone
  exact hnE (fun j hj => hnone j hj)

/-- Along almost every common Gaussian draw, every positive margin below
the growing scale eventually forces the line-graph obstruction. -/
theorem gaussian_path_ae_no_twinLineModel_growing_cutoff {ρ : Type*} [DecidableEq ρ] :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ S : Set (PathLabel n),
        (∀ l, clawCutoffScale n - ε < |pathPauliDisorderShell ω n l| → l ∈ S) →
        IsEmpty (TwinLineModel (pathFrustrationAdj S) ρ) := by
  have h (k : ℕ) := gaussian_ae_eventually_clawBlock_at_growing_cutoff
    (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hmargin : 1 / ((k : ℝ) + 1) ≤ ε := by
    have h := (div_lt_iff₀ hε).mp hk
    apply (div_le_iff₀ (show 0 < (k : ℝ) + 1 by positivity)).mpr
    nlinarith only [h, hε]
  filter_upwards [hω k] with n hn S hS
  obtain ⟨j, hj, hb⟩ := hn
  have hj' := Finset.mem_range.mp hj
  exact path_no_twinLineModel_of_clawBlock ω n j (by omega) _ hb S fun l hl =>
    hS l ((sub_le_sub_left hmargin _).trans_lt hl)

/-- The absolute Gaussian tail is bounded by twice the one-sided Chernoff bound. -/
theorem gaussianAbsoluteTailMass_exp_upper {t : ℝ} (ht : 0 ≤ t) :
    gaussianAbsoluteTailMass t ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2))) := by
  let μ := gaussianReal 0 1
  have hmap : μ.map (fun x : ℝ => -x) = μ := by
    simpa [μ] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1))
  have hset : (fun x : ℝ => -x) ⁻¹' Iic (-t) = Ici t := by
    ext x
    simp
  have hsym : μ (Ici t) = μ (Iic (-t)) := by
    rw [← hset, ← Measure.map_apply measurable_neg measurableSet_Iic, hmap]
  have hsubset : {x : ℝ | t < |x|} ⊆ Iic (-t) ∪ Ici t := by
    intro x hx
    change t < |x| at hx
    by_cases h : 0 ≤ x
    · rw [abs_of_nonneg h] at hx
      exact Or.inr hx.le
    · rw [abs_of_nonpos (le_of_not_ge h)] at hx
      exact Or.inl (by change x ≤ -t; linarith only [hx])
  change μ {x : ℝ | t < |x|} ≤ _
  calc
    _ ≤ μ (Iic (-t) ∪ Ici t) := measure_mono hsubset
    _ ≤ μ (Iic (-t)) + μ (Ici t) := measure_union_le _ _
    _ ≤ _ := by
      rw [hsym, two_mul, ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      exact add_le_add (gaussianReal_Iic_neg_le ht) (gaussianReal_Iic_neg_le ht)

/-- A finite union bound for finding any certificate among m blocks. -/
theorem gaussian_measure_someClawBlock_le (t : ℝ) (m : ℕ) :
    pathPauliDisorderLaw (noClawBlockEvent t m)ᶜ ≤
      (m : ENNReal) * gaussianAbsoluteTailMass t ^ 6 := by
  let ν : Measure (PathPauliBlockLabel → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
  letI : IsProbabilityMeasure ν := by unfold ν; infer_instance
  let E (j : ℕ) : Set PathPauliDisorder := {ω | pathPauliBlock ω j ∈ clawBlockEvent t}
  have he : (noClawBlockEvent t m)ᶜ = ⋃ j ∈ Finset.range m, E j := by
    ext ω
    change (¬∀ j ∈ Finset.range m, pathPauliBlock ω j ∉ clawBlockEvent t) ↔ _
    push Not
    simp only [E, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor <;> rintro ⟨j, hj, hb⟩ <;> exact ⟨j, hj, hb⟩
  have hm : MeasurePreserving pathPauliBlock pathPauliDisorderLaw
      (Measure.infinitePi fun _ : ℕ => ν) := measurePreserving_paired_rows _
  have hE (j : ℕ) : pathPauliDisorderLaw (E j) = gaussianAbsoluteTailMass t ^ 6 := by
    have H := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).comp hm
    change pathPauliDisorderLaw ((Function.eval j ∘ pathPauliBlock) ⁻¹' clawBlockEvent t) = _
    rw [← Measure.map_apply H.measurable (measurableSet_clawBlockEvent t), H.map_eq]
    exact gaussian_measure_clawBlockEvent t
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range m, pathPauliDisorderLaw (E j) := measure_biUnion_finset_le _ _
    _ = _ := by simp only [hE, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Above the growing scale the probability of any six-coordinate
certificate decays with the positive margin. -/
theorem gaussian_measure_someClawBlock_above_growingCutoff (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    pathPauliDisorderLaw (noClawBlockEvent (clawCutoffScale n + ε) ((n + 1) / 2))ᶜ ≤
      ENNReal.ofReal (32 * Real.exp (-(3 * ε ^ 2) - 6 * ε * clawCutoffScale n)) := by
  let r := clawCutoffScale n
  let N := (n : ℝ) + 1
  let m := (n + 1) / 2
  let t := r + ε
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 ≤ t := add_nonneg (Real.sqrt_nonneg _) hε
  have hm : (m : ℝ) ≤ N / 2 := by
    have hh : 2 * m ≤ n + 1 := by dsimp [m]; omega
    have hreal : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hh
    change (m : ℝ) ≤ ((n : ℝ) + 1) / 2
    linarith only [hreal]
  have hscale : Real.log N = 3 * r ^ 2 := by
    have h : r ^ 2 = Real.log N / 3 := clawCutoffScale_sq n
    linarith only [h]
  have harg : -(3 * t ^ 2) = -(3 * ε ^ 2) - 6 * ε * r - Real.log N := by
    rw [hscale]
    dsimp [t]
    ring
  have hexp : (2 * Real.exp (-(t ^ 2 / 2))) ^ 6 =
      64 * (Real.exp (-(3 * ε ^ 2) - 6 * ε * r) / N) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have hc : ((6 : ℕ) : ℝ) * -(t ^ 2 / 2) = -(3 * t ^ 2) := by
      push_cast
      ring
    rw [hc, harg, Real.exp_sub, Real.exp_log hN]
    norm_num
  change pathPauliDisorderLaw (noClawBlockEvent t m)ᶜ ≤ _
  refine (gaussian_measure_someClawBlock_le t m).trans ?_
  calc
    _ ≤ (m : ENNReal) * ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2))) ^ 6 :=
      mul_le_mul_right (pow_le_pow_left' (gaussianAbsoluteTailMass_exp_upper ht) 6) _
    _ = ENNReal.ofReal ((m : ℝ) * (2 * Real.exp (-(t ^ 2 / 2))) ^ 6) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [hexp]
      calc
        _ ≤ (N / 2) * (64 * (Real.exp (-(3 * ε ^ 2) - 6 * ε * r) / N)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = _ := by field_simp [hN.ne']; ring

/-- At every fixed positive margin above the scale the certificate probability tends to zero. -/
theorem tendsto_gaussian_measure_claw_above_growingCutoff {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (pathPauliDisorderLaw (noClawBlockEvent (clawCutoffScale n + ε) ((n + 1) / 2))ᶜ).toReal)
      atTop (𝓝 0) := by
  have hc : 0 < 6 * ε := by positivity
  have ht : Tendsto (fun n : ℕ => 6 * ε * clawCutoffScale n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_le_clawCutoffScale (le_max_left (0 : ℝ) (b / (6 * ε)))] with n hn
    change b ≤ 6 * ε * clawCutoffScale n
    have hb := (div_le_iff₀ hc).mp ((le_max_right (0 : ℝ) (b / (6 * ε))).trans hn)
    simpa only [mul_comm] using hb
  have hlim : Tendsto (fun n : ℕ => 32 * Real.exp (-(3 * ε ^ 2) - 6 * ε * clawCutoffScale n))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 32 * Real.exp (-(3 * ε ^ 2)))).mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht)
    simpa only [Function.comp_def, mul_zero, mul_assoc, ← Real.exp_add, ← sub_eq_add_neg] using h
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hlim
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (gaussian_measure_someClawBlock_above_growingCutoff n hε.le)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

#print axioms gaussianAbsoluteTailMass_interval_lower
#print axioms gaussian_path_ae_no_twinLineModel_growing_cutoff
#print axioms gaussian_measure_someClawBlock_above_growingCutoff
#print axioms tendsto_gaussian_measure_claw_above_growingCutoff

end

end GaloisForLFunctions.HTGeometry
