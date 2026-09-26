import GaloisForLFunctions.RHTower.FermiNymanWitnessExponentZeroRigidity

/-!
# The Riemann hypothesis is dyadic self-similarity of the square-integrable witnesses

For the alternating Nyman–Beurling system `φ_b(t) = {1/(bt)} − 2{1/(2bt)}` (`b ≥ 1`):

`RH ⟺ every continuous square-integrable witness w on (0,1] satisfies w(t/2) = w(t)`.

The direction `⇐` is `riemannHypothesis_of_fermiNymanWitness_selfSimilar` (a zero `ρ` with
`½ < Re ρ < 1` gives the witness `t^{ρ̄−1}`, which is not self-similar).  For `⇒`, a square-integrable
witness has Mellin exponent `½` with majorant `m(½ + ε) = O(ε^{−1/2})`.  Under RH, `Ξ(1 − z)` has no
zero off `Re z = ½`, and at a zero on that line the left form `−2^{−z} z(1−z)Φ₀(1−z)/Ξ(1−z)` has a
removable singularity: a pole of order `≥ 1` would exceed the bound `O(ε^{−1/2})` of the right form
`(1 − 2^{−z})W(z)` at `z₀ + ε`.  The regularized dyadic defect is therefore entire, and the proof of
`FermiNymanWitnessExponentZeroRigidity` (maximum modulus between the heights of Titchmarsh IX.7,
Liouville, Fourier uniqueness) applies verbatim.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

variable {w : ℝ → ℂ}

/-! ## Square-integrable witnesses have Mellin exponent `½` -/

theorem integral_rpow_two_mul_sub_two {x : ℝ} (hx : 1 / 2 < x) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * x - 2) = 1 / (2 * x - 1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith)]
  ring_nf

theorem integrableOn_rpow_two_mul_sub_two {x : ℝ} (hx : 1 / 2 < x) :
    IntegrableOn (fun t : ℝ => t ^ (2 * x - 2)) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegral.intervalIntegrable_rpow' (by linarith))

/-- `t^{x−1}|w| ≤ (λ t^{2x−2} + |w|²/λ)/2`. -/
theorem rpow_mul_le_amgm {t x lam y : ℝ} (ht : 0 < t) (hlam : 0 < lam) :
    t ^ (x - 1) * y ≤ (lam * t ^ (2 * x - 2) + y ^ 2 / lam) / 2 := by
  have hsq : t ^ (2 * x - 2) = (t ^ (x - 1)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; ring_nf
  rw [hsq, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have key : 0 ≤ (lam * t ^ (x - 1) - y) ^ 2 := sq_nonneg _
  have : lam * (t ^ (x - 1)) ^ 2 + y ^ 2 / lam - t ^ (x - 1) * y * 2 =
      (lam * t ^ (x - 1) - y) ^ 2 / lam := by field_simp; ring
  have h2 : 0 ≤ (lam * t ^ (x - 1) - y) ^ 2 / lam := div_nonneg key hlam.le
  linarith

/-- A continuous square-integrable witness has Mellin exponent `½`. -/
theorem isMellinFermiWitness_half_of_sq (hc : ContinuousOn w (Ioc 0 1))
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (ho : ∀ b : ℝ, 1 ≤ b → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * w t = 0) :
    IsMellinFermiWitness w (1 / 2) := by
  refine ⟨hc, by norm_num, by norm_num, fun x hx => ?_, ho⟩
  have hI : IntegrableOn (fun t : ℝ => (1 * t ^ (2 * x - 2) + ‖w t‖ ^ 2 / 1) / 2) (Ioc 0 1) :=
    (((integrableOn_rpow_two_mul_sub_two hx).const_mul 1).add (hsq.div_const 1)).div_const 2
  refine hI.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne').mul hc.norm
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))]
    exact rpow_mul_le_amgm ht.1 one_pos

/-- **The majorant rate** `m(x) ≤ (1 + ∫|w|²)/(2√(2x − 1))` for `x > ½`. -/
theorem witnessMajorant_le_of_sq (hc : ContinuousOn w (Ioc 0 1))
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1)) {x : ℝ} (hx : 1 / 2 < x) :
    witnessMajorant w x ≤
      (1 + ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2) / (2 * Real.sqrt (2 * x - 1)) := by
  set S := ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 with hS
  set lam := Real.sqrt (2 * x - 1) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by linarith)
  have hlam2 : lam ^ 2 = 2 * x - 1 := Real.sq_sqrt (by linarith)
  have hI : IntegrableOn (fun t : ℝ => (lam * t ^ (2 * x - 2) + ‖w t‖ ^ 2 / lam) / 2) (Ioc 0 1) :=
    (((integrableOn_rpow_two_mul_sub_two hx).const_mul lam).add (hsq.div_const lam)).div_const 2
  have hle : witnessMajorant w x ≤
      ∫ t in Ioc (0 : ℝ) 1, (lam * t ^ (2 * x - 2) + ‖w t‖ ^ 2 / lam) / 2 := by
    unfold witnessMajorant
    refine setIntegral_mono_on ?_ hI measurableSet_Ioc (fun t ht => rpow_mul_le_amgm ht.1 hlam0)
    have hI1 : IntegrableOn (fun t : ℝ => (1 * t ^ (2 * x - 2) + ‖w t‖ ^ 2 / 1) / 2) (Ioc 0 1) :=
      (((integrableOn_rpow_two_mul_sub_two hx).const_mul 1).add (hsq.div_const 1)).div_const 2
    refine hI1.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne').mul hc.norm
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))]
      exact rpow_mul_le_amgm ht.1 one_pos
  have hval : (∫ t in Ioc (0 : ℝ) 1, (lam * t ^ (2 * x - 2) + ‖w t‖ ^ 2 / lam) / 2) =
      (lam * (1 / (2 * x - 1)) + S / lam) / 2 := by
    rw [integral_div, integral_add ((integrableOn_rpow_two_mul_sub_two hx).const_mul lam)
      (hsq.div_const lam), integral_const_mul, integral_div, integral_rpow_two_mul_sub_two hx]
  rw [hval] at hle
  refine hle.trans (le_of_eq ?_)
  rw [← hlam2]
  field_simp

/-! ## `Ξ(1 − z)` under RH -/

/-- Under RH, `Ξ(1 − z) = −z ζ(1 − z)` has no zero with `Re z < 1` off the line `Re z = ½`. -/
theorem zetaEntire_one_sub_ne_zero_of_rh (hRH : RiemannHypothesis) {z : ℂ} (hz1 : z.re < 1)
    (hz : z.re ≠ 1 / 2) : zetaEntire (1 - z) ≠ 0 := by
  by_cases h0 : z = 0
  · rw [h0, sub_zero]
    exact Sieve.zetaEntire_ne_zero_of_one_le_re (by simp)
  have hne1 : (1 : ℂ) - z ≠ 1 := by intro h; apply h0; linear_combination -h
  rw [zetaEntire_eq hne1]
  refine mul_ne_zero (sub_ne_zero.2 hne1) ?_
  by_cases hre : 1 ≤ (1 - z).re
  · exact riemannZeta_ne_zero_of_one_le_re hre
  · intro hζ
    have hpos : 0 < (1 - z).re := by simp; linarith
    have htriv : ¬∃ n : ℕ, (1 - z) = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp at this
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have := hRH (1 - z) hζ htriv hne1
    simp at this
    exact hz (by linarith)

/-! ## The regularized dyadic defect -/

open Classical in
/-- The dyadic defect on `Re z > ½`, the left form where `Ξ(1 − z) ≠ 0`, and the limit of the left
form at the remaining points. -/
def dyadicDefectReg (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  if 1 / 2 < z.re then dyadicDefectRight w z
  else if zetaEntire (1 - z) ≠ 0 then dyadicDefectLeft w z
  else limUnder (𝓝[≠] z) (dyadicDefectLeft w)

theorem dyadicDefectReg_eq_dyadicDefect {z : ℂ} (h : 1 / 2 < z.re ∨ zetaEntire (1 - z) ≠ 0) :
    dyadicDefectReg w z = dyadicDefect w (1 / 2) z := by
  unfold dyadicDefectReg dyadicDefect
  by_cases hz : 1 / 2 < z.re
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz, if_pos (h.resolve_left hz)]

theorem norm_one_sub_two_cpow_neg_le {z : ℂ} (hz : 0 ≤ z.re) : ‖1 - (2 : ℂ) ^ (-z)‖ ≤ 2 := by
  have h : ‖(2 : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [norm_two_cpow, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  calc ‖1 - (2 : ℂ) ^ (-z)‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

theorem analyticAt_leftNumerator (hw : IsMellinFermiWitness w (1 / 2)) {z : ℂ}
    (hz : z.re < 1) :
    AnalyticAt ℂ (fun u : ℂ => -((2 : ℂ) ^ (-u)) * u * (1 - u) * correlationMellin w (1 - u)) z := by
  refine DifferentiableOn.analyticAt (s := {u : ℂ | u.re < 1}) ?_
    ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz)
  intro u hu
  have hu' : 0 < (1 - u).re := by simp; exact hu
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (1 : ℂ) - v) u :=
    (differentiableAt_const _).sub differentiableAt_id
  have hΦ : DifferentiableAt ℂ (fun v : ℂ => correlationMellin w (1 - v)) u :=
    (hw.differentiableAt_correlationMellin hu').comp u h1
  have h2 : DifferentiableAt ℂ (fun v : ℂ => -((2 : ℂ) ^ (-v))) u :=
    ((differentiableAt_id.neg).const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).neg
  exact (((h2.mul differentiableAt_id).mul h1).mul hΦ).differentiableWithinAt

/-- **Removability on the critical line.**  Under RH, for a square-integrable witness the left form
has nonnegative meromorphic order at every point of `Re z = ½`. -/
theorem meromorphicOrderAt_dyadicDefectLeft_nonneg (hRH : RiemannHypothesis)
    (hw : IsMellinFermiWitness w (1 / 2)) {B : ℝ}
    (hB : ∀ x : ℝ, 1 / 2 < x → witnessMajorant w x ≤ B / Real.sqrt (2 * x - 1)) {z : ℂ}
    (hz : z.re = 1 / 2) :
    MeromorphicAt (dyadicDefectLeft w) z ∧ 0 ≤ meromorphicOrderAt (dyadicDefectLeft w) z := by
  have hmero : MeromorphicAt (dyadicDefectLeft w) z := by
    have hnum := (analyticAt_leftNumerator hw (z := z) (by linarith)).meromorphicAt
    have hden : AnalyticAt ℂ (fun u : ℂ => zetaEntire (1 - u)) z :=
      (differentiable_zetaEntire.comp ((differentiable_const _).sub differentiable_id)).analyticAt z
    have := hnum.div hden.meromorphicAt
    refine this.congr ?_
    exact Eventually.of_forall fun u => by simp [dyadicDefectLeft, Pi.div_apply]
  refine ⟨hmero, ?_⟩
  by_contra hneg
  rw [not_le] at hneg
  have hne_top : meromorphicOrderAt (dyadicDefectLeft w) z ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne_top
  rw [← hn] at hneg
  have hn0 : n < 0 := by exact_mod_cast hneg
  obtain ⟨g, hg, hg0, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 hn.symm
  -- approach along `z + ε`, `ε → 0⁺`
  have hmap : Tendsto (fun ε : ℝ => z + (ε : ℂ)) (𝓝[>] 0) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => z + (ε : ℂ)) (𝓝 0) (𝓝 (z + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero]
      exact ne_of_gt hε
  have hg_lim : Tendsto (fun ε : ℝ => g (z + (ε : ℂ))) (𝓝[>] 0) (𝓝 (g z)) :=
    (hg.continuousAt.tendsto.comp (hmap.mono_right nhdsWithin_le_nhds))
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖g (z + (ε : ℂ))‖ ≤ 2 * B * Real.sqrt ε := by
    filter_upwards [hmap.eventually hgeq, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)]
      with ε hε hε2
    have hε0 : 0 < ε := hε2.1
    have hre : (z + (ε : ℂ)).re = 1 / 2 + ε := by simp [hz]
    have hΞ : zetaEntire (1 - (z + (ε : ℂ))) ≠ 0 :=
      zetaEntire_one_sub_ne_zero_of_rh hRH (by rw [hre]; linarith [hε2.2])
        (by rw [hre]; linarith)
    have hRL := hw.dyadicDefectRight_eq_left (z := z + (ε : ℂ)) (by rw [hre]; linarith)
      (by rw [hre]; linarith [hε2.2]) hΞ
    have hR : ‖dyadicDefectRight w (z + (ε : ℂ))‖ ≤ 2 * (B / Real.sqrt (2 * ε)) := by
      unfold dyadicDefectRight
      rw [norm_mul]
      have hW := hw.norm_witnessMellin_le (z := z + (ε : ℂ)) (by rw [hre]; linarith)
      rw [hre] at hW
      have hm := hB (1 / 2 + ε) (by linarith)
      rw [show 2 * (1 / 2 + ε) - 1 = 2 * ε by ring] at hm
      exact mul_le_mul (norm_one_sub_two_cpow_neg_le (by rw [hre]; linarith)) (hW.trans hm)
        (norm_nonneg _) (by norm_num)
    rw [add_sub_cancel_left] at hε
    have hεC : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε0.ne'
    have hgε : g (z + (ε : ℂ)) = (ε : ℂ) ^ (-n) * dyadicDefectLeft w (z + (ε : ℂ)) := by
      rw [hε, smul_eq_mul, ← mul_assoc, ← zpow_add₀ hεC, neg_add_cancel, zpow_zero, one_mul]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = (m : ℤ) := ⟨(-n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hm1 : m ≠ 0 := by omega
    have hnorm : ‖(ε : ℂ) ^ (-n)‖ = ε ^ m := by
      rw [hm, zpow_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    have hεm : ε ^ m ≤ ε := pow_le_of_le_one hε0.le (by linarith [hε2.2]) hm1
    have hB0 : 0 ≤ B := by
      have h1 := hB 1 (by norm_num)
      rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, Real.sqrt_one, div_one] at h1
      exact le_trans (witnessMajorant_nonneg w 1) h1
    have hsq2 : Real.sqrt (2 * ε) = Real.sqrt 2 * Real.sqrt ε := Real.sqrt_mul (by norm_num) ε
    have hsqε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
    have hsq2' : 1 ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [hgε, norm_mul, hnorm, ← hRL]
    calc ε ^ m * ‖dyadicDefectRight w (z + (ε : ℂ))‖
        ≤ ε * (2 * (B / Real.sqrt (2 * ε))) :=
          mul_le_mul hεm hR (norm_nonneg _) hε0.le
      _ = (Real.sqrt ε * Real.sqrt ε) * (2 * (B / (Real.sqrt 2 * Real.sqrt ε))) := by
          rw [Real.mul_self_sqrt hε0.le, hsq2]
      _ = 2 * B * Real.sqrt ε / Real.sqrt 2 := by field_simp
      _ ≤ 2 * B * Real.sqrt ε := div_le_self (by positivity) hsq2'
  have hlim0 : Tendsto (fun ε : ℝ => 2 * B * Real.sqrt ε) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => 2 * B * Real.sqrt ε) (𝓝 0) (𝓝 (2 * B * Real.sqrt 0)) :=
      (continuous_const.mul Real.continuous_sqrt).tendsto 0
    rw [Real.sqrt_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto ((continuous_norm.tendsto _).comp hg_lim) hlim0 hbound
  exact hg0 (norm_le_zero_iff.1 hle)

/-- **The regularized dyadic defect is entire** under RH, for a square-integrable witness. -/
theorem differentiable_dyadicDefectReg (hRH : RiemannHypothesis)
    (hw : IsMellinFermiWitness w (1 / 2)) {B : ℝ}
    (hB : ∀ x : ℝ, 1 / 2 < x → witnessMajorant w x ≤ B / Real.sqrt (2 * x - 1)) :
    Differentiable ℂ (dyadicDefectReg w) := by
  intro z
  rcases lt_trichotomy z.re (1 / 2) with hlt | heq | hgt
  · have hΞz := zetaEntire_one_sub_ne_zero_of_rh hRH (z := z) (by linarith) (by linarith)
    have hev : dyadicDefectReg w =ᶠ[𝓝 z] dyadicDefectLeft w := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt] with u hu
      have hu' : u.re < 1 / 2 := hu
      unfold dyadicDefectReg
      rw [if_neg (by linarith),
        if_pos (zetaEntire_one_sub_ne_zero_of_rh hRH (by linarith) (by linarith))]
    have h1 : 0 < (1 - z).re := by simp; linarith
    exact (hw.differentiableAt_dyadicDefectLeft h1 hΞz).congr_of_eventuallyEq hev
  · by_cases hΞz : zetaEntire (1 - z) ≠ 0
    · have hopen : IsOpen ({u : ℂ | |u.re - 1 / 2| < 1 / 4} ∩
          {u : ℂ | zetaEntire (1 - u) ≠ 0}) := by
        refine (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
          continuous_const).inter ?_
        exact isOpen_ne_fun (differentiable_zetaEntire.continuous.comp
          (continuous_const.sub continuous_id)) continuous_const
      have hmem : z ∈ {u : ℂ | |u.re - 1 / 2| < 1 / 4} ∩ {u : ℂ | zetaEntire (1 - u) ≠ 0} := by
        refine ⟨?_, hΞz⟩
        show |z.re - 1 / 2| < 1 / 4
        rw [heq, sub_self, abs_zero]; norm_num
      have hev : dyadicDefectReg w =ᶠ[𝓝 z] dyadicDefectLeft w := by
        filter_upwards [hopen.mem_nhds hmem] with u hu
        obtain ⟨hre, hΞu⟩ := hu
        simp only [mem_setOf_eq] at hre hΞu
        unfold dyadicDefectReg
        split_ifs with hup
        · exact hw.dyadicDefectRight_eq_left hup (by linarith [(abs_lt.1 hre).2]) hΞu
        · rfl
      have h1 : 0 < (1 - z).re := by simp; linarith
      exact (hw.differentiableAt_dyadicDefectLeft h1 hΞz).congr_of_eventuallyEq hev
    · have hΞ0 : zetaEntire (1 - z) = 0 := not_not.1 hΞz
      obtain ⟨hmero, hord⟩ := meromorphicOrderAt_dyadicDefectLeft_nonneg hRH hw hB heq
      have hΞan : AnalyticAt ℂ (fun u : ℂ => zetaEntire (1 - u)) z :=
        (differentiable_zetaEntire.comp ((differentiable_const _).sub differentiable_id)).analyticAt z
      have hpunct : ∀ᶠ u in 𝓝[≠] z, zetaEntire (1 - u) ≠ 0 := by
        rcases hΞan.eventually_eq_zero_or_eventually_ne_zero with h | h
        · exfalso
          have hmap : Tendsto (fun ε : ℝ => z + (ε : ℂ)) (𝓝[>] 0) (𝓝 z) := by
            have : Tendsto (fun ε : ℝ => z + (ε : ℂ)) (𝓝 0) (𝓝 (z + ((0 : ℝ) : ℂ))) :=
              (continuous_const.add Complex.continuous_ofReal).tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          obtain ⟨ε, hε, hε2⟩ := ((hmap.eventually h).and
            (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
          have hre : (z + (ε : ℂ)).re = 1 / 2 + ε := by simp [heq]
          exact zetaEntire_one_sub_ne_zero_of_rh hRH (by rw [hre]; linarith [hε2.2])
            (by rw [hre]; linarith [hε2.1]) hε
        · exact h
      have hRegL : dyadicDefectReg w =ᶠ[𝓝[≠] z] dyadicDefectLeft w := by
        filter_upwards [hpunct, nhdsWithin_le_nhds
          ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
            (show z.re < 1 by linarith))] with u hu hu1
        unfold dyadicDefectReg
        split_ifs with h1
        · exact hw.dyadicDefectRight_eq_left h1 hu1 hu
        · rfl
      obtain ⟨h, hh, hLh⟩ : ∃ h : ℂ → ℂ, AnalyticAt ℂ h z ∧ dyadicDefectLeft w =ᶠ[𝓝[≠] z] h := by
        rcases eq_or_ne (meromorphicOrderAt (dyadicDefectLeft w) z) ⊤ with htop | hntop
        · exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.1 htop⟩
        · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hntop
          have hn0 : 0 ≤ n := by rw [← hn] at hord; exact_mod_cast hord
          obtain ⟨g, hg, _, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 hn.symm
          lift n to ℕ using hn0
          refine ⟨fun u => (u - z) ^ n * g u,
            ((analyticAt_id.sub analyticAt_const).pow n).mul hg, ?_⟩
          filter_upwards [hgeq] with u hu
          rw [hu, zpow_natCast, smul_eq_mul]
      have hval : dyadicDefectReg w z = h z := by
        unfold dyadicDefectReg
        rw [if_neg (by linarith), if_neg (not_not.2 hΞ0)]
        exact ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hLh.symm).limUnder_eq
      have hev : dyadicDefectReg w =ᶠ[𝓝 z] h := by
        have h1 := hRegL.trans hLh
        rw [EventuallyEq, eventually_nhdsWithin_iff] at h1
        filter_upwards [h1] with u hu
        by_cases huz : u = z
        · rw [huz, hval]
        · exact hu huz
      exact hh.differentiableAt.congr_of_eventuallyEq hev
  · have hev : dyadicDefectReg w =ᶠ[𝓝 z] dyadicDefectRight w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hgt] with u hu
      unfold dyadicDefectReg
      rw [if_pos hu]
    exact (hw.differentiableAt_dyadicDefectRight hgt).congr_of_eventuallyEq hev

/-! ## The transform and its vanishing -/

/-- The regularized transform `U(z) = 2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)`. -/
def dyadicDefectTransformReg (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ z * (dyadicDefectReg w z - upperWitnessMellin w z)

theorem dyadicDefectTransformReg_eq {z : ℂ} (h : 1 / 2 < z.re ∨ zetaEntire (1 - z) ≠ 0) :
    dyadicDefectTransformReg w z = dyadicDefectTransform w (1 / 2) z := by
  unfold dyadicDefectTransformReg dyadicDefectTransform
  rw [dyadicDefectReg_eq_dyadicDefect h]

theorem zetaEntire_one_sub_ne_zero_of_zeta {z : ℂ} (hz0 : z ≠ 0) (hζ : riemannZeta (1 - z) ≠ 0) :
    zetaEntire (1 - z) ≠ 0 := by
  have hne1 : (1 : ℂ) - z ≠ 1 := by intro h; apply hz0; linear_combination -h
  rw [zetaEntire_eq hne1]
  exact mul_ne_zero (sub_ne_zero.2 hne1) hζ

/-- **Under RH, a square-integrable-rate witness of Mellin exponent `½` is self-similar.** -/
theorem IsMellinFermiWitness.selfSimilar_of_rh (hRH : RiemannHypothesis)
    (hw : IsMellinFermiWitness w (1 / 2)) {B : ℝ}
    (hB : ∀ x : ℝ, 1 / 2 < x → witnessMajorant w x ≤ B / Real.sqrt (2 * x - 1)) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  have hdiff : Differentiable ℂ (dyadicDefectTransformReg w) := by
    intro z
    exact (differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).mul
      ((differentiable_dyadicDefectReg hRH hw hB z).sub (hw.differentiable_upperWitnessMellin z))
  have hgrowth := exists_polyGrowth_of_zetaInv_bounds hdiff (x₁ := 3 / 4)
    (c := 12 * witnessMajorant w 1) (by norm_num) (by norm_num) (rightDefectBound_nonneg w _)
    (upperDefectBound_nonneg w) (by have := witnessMajorant_nonneg w 1; positivity)
    (fun z hz => by
      rw [dyadicDefectTransformReg_eq (Or.inl (by linarith))]
      exact hw.norm_dyadicDefectTransform_le_right (by norm_num) (by norm_num) hz)
    (fun z hz hz0 hζ => by
      rw [dyadicDefectTransformReg_eq (Or.inr (zetaEntire_one_sub_ne_zero_of_zeta hz0 hζ))]
      have h := hw.norm_dyadicDefectTransform_le_left (by linarith) hz0 (fun _ => hζ)
      have hm := witnessMajorant_nonneg w 1
      have h3 : 3 * witnessMajorant w 1 / (1 - z.re) ≤ 12 * witnessMajorant w 1 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      rw [one_div ‖riemannZeta (1 - z)‖, ← norm_inv] at h
      refine h.trans (add_le_add ?_ le_rfl)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
        (norm_nonneg _))
  have hlim : Tendsto (fun n : ℕ => dyadicDefectTransformReg w ((n : ℂ) + 1)) atTop (𝓝 0) := by
    refine hw.tendsto_dyadicDefectTransform_nat.congr (fun n => ?_)
    rw [dyadicDefectTransformReg_eq (Or.inl ?_)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    simp; linarith
  have hzero := eq_zero_of_polyGrowth_of_tendsto_nat hdiff hgrowth hlim
  refine selfSimilar_of_mellin_lowerDefect hw.cont hw.integrable_lowerDefect (fun z hz => ?_) ht
  have h := hzero z
  rw [dyadicDefectTransformReg_eq (Or.inl (by rw [hz]; norm_num)),
    hw.dyadicDefectTransform_eq_of_lt_re (by rw [hz]; norm_num)] at h
  have h2 : (2 : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]; exact Complex.exp_ne_zero _
  unfold lowerDefect
  rw [mellin_indicator_eq_setIntegral le_rfl]
  exact (mul_eq_zero.1 h).resolve_left h2

/-- **The Riemann hypothesis is the dyadic self-similarity of the square-integrable witnesses of the
alternating Nyman–Beurling system.** -/
theorem riemannHypothesis_iff_fermiNymanWitness_selfSimilar :
    RiemannHypothesis ↔
      ∀ w : ℝ → ℂ, IsFermiNymanWitness w → ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t := by
  refine ⟨fun hRH w hw t ht => ?_, riemannHypothesis_of_fermiNymanWitness_selfSimilar⟩
  set v : ℝ → ℂ := fun u => (starRingEnd ℂ) (w u) with hv
  have hvc : ContinuousOn v (Ioc 0 1) := Complex.continuous_conj.comp_continuousOn hw.1
  have hvsq : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioc 0 1) := by
    simpa [hv, Complex.norm_conj] using hw.2.1
  have hvw : IsMellinFermiWitness v (1 / 2) :=
    isMellinFermiWitness_half_of_sq hvc hvsq (fun b hb => hw.2.2 b hb)
  have h := hvw.selfSimilar_of_rh hRH (B := (1 + ∫ t in Ioc (0 : ℝ) 1, ‖v t‖ ^ 2) / 2)
    (fun x hx => by rw [div_div]; exact witnessMajorant_le_of_sq hvc hvsq hx) ht
  have := congrArg (starRingEnd ℂ) h
  simpa [hv] using this

/-- **RH is the half-mass identity** `∫_0^{1/2}|w|² = ½ ∫_0^1 |w|²` on the witness class. -/
theorem riemannHypothesis_iff_fermiNymanWitness_halfMass :
    RiemannHypothesis ↔ ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
      (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) = (1 / 2) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 :=
  ⟨fun hRH w hw => integral_half_normSq_of_selfSimilar
      (riemannHypothesis_iff_fermiNymanWitness_selfSimilar.1 hRH w hw),
    riemannHypothesis_of_fermiNymanWitness_halfMass⟩

/-- **RH is the positivity of the dyadic Hermitian form** `q(w) = ∫_0^{1/2}|w|² − ½∫_0^1|w|² ≥ 0` on
the witness class (equivalently: the dyadic dilation is non-contracting on witnesses). -/
theorem riemannHypothesis_iff_fermiNymanWitness_halfMass_le :
    RiemannHypothesis ↔ ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
      (1 / 2) * (∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2) ≤ ∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2 :=
  ⟨fun hRH w hw => (riemannHypothesis_iff_fermiNymanWitness_halfMass.1 hRH w hw).ge,
    riemannHypothesis_of_fermiNymanWitness_halfMass_le⟩

end RHTower
