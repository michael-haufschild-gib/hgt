import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeCapacityOfTheDominantZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverEnergyGrowthAtTheZeroAbscissa

/-!
# The escape energy at the abscissa pays the residues

`TheEscapeAlternative` shows that an uncancelled zero `ρ` with `Re ρ > ½ + ε` makes the receiver
energy `E_ε(T) = Σ_{n ≤ T} A_ε(n)²/(n(n+1))` exceed every `O(T^κ)` with `κ < 2θ`,
`θ = Re ρ − ε − ½`. At the exponent `κ = 2θ` itself it says nothing. This file settles the endpoint
with an explicit constant.

* **The Abelian bound** (`lintegral_exp_mul_le_of_horizon`). If `∫_0^L f ≤ Φ(L)` for a nonnegative
  `f`, then `∫_0^∞ e^{−su} f ≤ ∫_0^∞ s e^{−sL} Φ(L) dL` (Tonelli on `e^{−su} = ∫_u^∞ s e^{−sL} dL`).
* **The endpoint law** (`residue_mass_le_of_energy_le`). If the receiver is dominated at `θ` by a
  finite set `s` of simple zeros on `Re ρ = θ + ½ + ε` and `E_ε(T) ≤ C (T+1)^{2θ}` for all `T`, then
  `Σ_{ρ ∈ s} ‖r_ρ‖² ≤ 2θ C`, `r_ρ = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`: the energy majorant at the exact
  exponent pays the residue mass of the dominant zeros. The Abel energy is bounded through the
  Abelian bound and the capacity law of `TheAbelEscapeCapacityOfTheDominantZeros` bounds it below.
* **Unconditionally at the zero abscissa** (`residue_mass_le_of_energy_le_at_zeroAbscissa`). By
  `exists_receiver_energy_le_of_zeroAbscissa` every set of simple zeros on the line
  `Re ρ = Θ`, `Θ` the zero abscissa, is dominant at `θ = Θ − ε − ½` for `0 < ε < Θ − ½`: so
  `E_ε(T) ≤ C (T+1)^{2θ}` for all `T` forces `C ≥ Σ_ρ ‖r_ρ‖²/(2θ)`.

So escape is not only a growth exponent: at its exponent the energy carries a constant at least the
total residue mass of the dominant zeros over `2θ`.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (dampedMobiusEnergy)

/-! ### The Abelian bound -/

/-- `∫_{u}^{∞} s e^{−sL} dL = e^{−su}`, in `ℝ≥0∞`. -/
theorem lintegral_Ioi_exp_tail {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ∫⁻ L in Ioi u, ENNReal.ofReal (s * Real.exp (-(s * L))) =
      ENNReal.ofReal (Real.exp (-(s * u))) := by
  have hint : IntegrableOn (fun L : ℝ => s * Real.exp (-(s * L))) (Ioi u) := by
    have := (integrableOn_exp_mul_Ioi (show -s < 0 by linarith) u).const_mul s
    exact Integrable.congr this (Eventually.of_forall fun L => by ring_nf)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun L => by positivity)]
  congr 1
  have h := integral_exp_mul_Ioi (show -s < 0 by linarith) u
  rw [integral_const_mul, show (fun L : ℝ => Real.exp (-(s * L))) = fun L => Real.exp (-s * L)
    from funext fun L => by ring_nf, h]
  field_simp

/-- `∫_0^∞ s e^{−sL}(SL + B) dL = S/s + B`, in `ℝ≥0∞`, for `S, B ≥ 0`. -/
theorem lintegral_Ioi_exp_linear {s S B : ℝ} (hs : 0 < s) (hS : 0 ≤ S) (hB : 0 ≤ B) :
    ∫⁻ L in Ioi (0 : ℝ), ENNReal.ofReal (s * Real.exp (-(s * L)) * (S * L + B)) =
      ENNReal.ofReal (S / s + B) := by
  have iL : IntegrableOn (fun L : ℝ => L * Real.exp (-(s * L))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := s) (by norm_num)
      le_rfl hs
    refine this.congr_fun (fun L hL => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    ring_nf
  have i0 : IntegrableOn (fun L : ℝ => Real.exp (-(s * L))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (show -s < 0 by linarith) 0
    exact Integrable.congr this (Eventually.of_forall fun L => by ring_nf)
  have hint : IntegrableOn (fun L : ℝ => s * Real.exp (-(s * L)) * (S * L + B)) (Ioi 0) := by
    refine Integrable.congr ((iL.const_mul (s * S)).add (i0.const_mul (s * B)))
      (Eventually.of_forall fun L => ?_)
    simp only [Pi.add_apply]; ring
  have h1 : ∫ L in Ioi (0 : ℝ), L * Real.exp (-(s * L)) = 1 / s ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hs
    rw [Real.Gamma_two, mul_one, Real.rpow_two, div_pow, one_pow] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have h0 : ∫ L in Ioi (0 : ℝ), Real.exp (-(s * L)) = 1 / s := by
    have := integral_exp_mul_Ioi (show -s < 0 by linarith) 0
    rw [show (fun L : ℝ => Real.exp (-(s * L))) = fun L => Real.exp (-s * L)
      from funext fun L => by ring_nf, this]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun L (hL : 0 < L) => by positivity)]
  congr 1
  have hsplit : ∫ L in Ioi (0 : ℝ), s * Real.exp (-(s * L)) * (S * L + B) =
      (s * S) * (∫ L in Ioi (0 : ℝ), L * Real.exp (-(s * L))) +
        (s * B) * (∫ L in Ioi (0 : ℝ), Real.exp (-(s * L))) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iL.const_mul _)
      (i0.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    ring
  rw [hsplit, h1, h0]
  field_simp


/-- **The Abelian bound.** If the horizon mass of `f` is dominated by `Φ`,
`∫_0^L f ≤ Φ(L)`, then `∫_0^∞ e^{−su} f(u) du ≤ ∫_0^∞ s e^{−sL} Φ(L) dL` (Tonelli:
`e^{−su} = ∫_u^∞ s e^{−sL} dL`). -/
theorem lintegral_exp_mul_le_of_horizon {f Φ : ℝ → ℝ} (hf : Measurable f) (hΦ : Measurable Φ)
    {s : ℝ} (hs : 0 < s)
    (hH : ∀ L, 0 < L → ∫⁻ u in Ioo 0 L, ENNReal.ofReal (f u) ≤ ENNReal.ofReal (Φ L)) :
    ∫⁻ u in Ioi 0, ENNReal.ofReal (Real.exp (-(s * u))) * ENNReal.ofReal (f u) ≤
      ∫⁻ L in Ioi 0, ENNReal.ofReal (s * Real.exp (-(s * L)) * Φ L) := by
  set g : ℝ → ENNReal := fun L => ENNReal.ofReal (s * Real.exp (-(s * L))) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (by fun_prop)
  set F : ℝ × ℝ → ENNReal := {p : ℝ × ℝ | p.1 < p.2}.indicator
    (fun p => g p.2 * ENNReal.ofReal (f p.1)) with hF
  have hFm : Measurable F :=
    (Measurable.mul (hgm.comp measurable_snd) (ENNReal.measurable_ofReal.comp
      (hf.comp measurable_fst))).indicator (measurableSet_lt measurable_fst measurable_snd)
  -- the inner integrals of `F` in each variable
  have hu : ∀ u, 0 < u → ∫⁻ L in Ioi 0, F (u, L) =
      ENNReal.ofReal (Real.exp (-(s * u))) * ENNReal.ofReal (f u) := by
    intro u hu
    have : (fun L => F (u, L)) = (Ioi u).indicator (fun L => g L * ENNReal.ofReal (f u)) := by
      funext L; simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Ioi]
    rw [this, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, sup_of_le_left hu.le, lintegral_mul_const _ hgm, lintegral_Ioi_exp_tail hs]
  have hL : ∀ L, 0 < L → ∫⁻ u in Ioi 0, F (u, L) =
      g L * ∫⁻ u in Ioo 0 L, ENNReal.ofReal (f u) := by
    intro L _
    have : (fun u => F (u, L)) = (Iio L).indicator (fun u => g L * ENNReal.ofReal (f u)) := by
      funext u; simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Iio]
    rw [this, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi]
    exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hf)
  calc ∫⁻ u in Ioi 0, ENNReal.ofReal (Real.exp (-(s * u))) * ENNReal.ofReal (f u)
      = ∫⁻ u in Ioi 0, ∫⁻ L in Ioi 0, F (u, L) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun u hu' => (hu u hu').symm
    _ = ∫⁻ L in Ioi 0, ∫⁻ u in Ioi 0, F (u, L) :=
        lintegral_lintegral_swap (hFm.comp_aemeasurable (by
          exact (measurable_fst.prodMk measurable_snd).aemeasurable))
    _ = ∫⁻ L in Ioi 0, g L * ∫⁻ u in Ioo 0 L, ENNReal.ofReal (f u) :=
        setLIntegral_congr_fun measurableSet_Ioi fun L hL' => hL L hL'
    _ ≤ ∫⁻ L in Ioi 0, ENNReal.ofReal (s * Real.exp (-(s * L)) * Φ L) := by
        refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (by fun_prop)) fun L hL' => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_right (hH L hL') _


/-- The power majorant: for `0 ≤ 2θ ≤ 1 < ⋯`, `2θ < s`, `C ≥ 0`,
`∫_0^∞ s e^{−sL} C (e^L + 1)^{2θ} dL ≤ sC/(s − 2θ) + C` (subadditivity of `x ↦ x^{2θ}`). -/
theorem lintegral_exp_mul_power_le {s θ C : ℝ} (hθ : 0 ≤ θ) (hθ1 : 2 * θ ≤ 1) (hs : 2 * θ < s)
    (hC : 0 ≤ C) :
    ∫⁻ L in Ioi 0, ENNReal.ofReal (s * Real.exp (-(s * L)) * (C * (Real.exp L + 1) ^ (2 * θ))) ≤
      ENNReal.ofReal (s * C / (s - 2 * θ) + C) := by
  have hs0 : 0 < s := by linarith
  have ia : IntegrableOn (fun L : ℝ => Real.exp (-(s - 2 * θ) * L)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have ib : IntegrableOn (fun L : ℝ => Real.exp (-s * L)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint : IntegrableOn (fun L : ℝ => s * C * Real.exp (-(s - 2 * θ) * L) +
      s * C * Real.exp (-s * L)) (Ioi 0) := (ia.const_mul _).add (ib.const_mul _)
  calc ∫⁻ L in Ioi 0, ENNReal.ofReal (s * Real.exp (-(s * L)) * (C * (Real.exp L + 1) ^ (2 * θ)))
      ≤ ∫⁻ L in Ioi 0, ENNReal.ofReal (s * C * Real.exp (-(s - 2 * θ) * L) +
          s * C * Real.exp (-s * L)) := by
        refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (by fun_prop)) fun L _ => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hsub : (Real.exp L + 1) ^ (2 * θ) ≤ Real.exp (2 * θ * L) + 1 := by
          have := Real.rpow_add_le_add_rpow (Real.exp_pos L).le zero_le_one (by linarith) hθ1
          rwa [Real.one_rpow, ← Real.exp_mul, mul_comm L] at this
        have he : Real.exp (-(s * L)) * Real.exp (2 * θ * L) = Real.exp (-(s - 2 * θ) * L) := by
          rw [← Real.exp_add]; ring_nf
        calc s * Real.exp (-(s * L)) * (C * (Real.exp L + 1) ^ (2 * θ))
            ≤ s * Real.exp (-(s * L)) * (C * (Real.exp (2 * θ * L) + 1)) := by gcongr
          _ = s * C * (Real.exp (-(s * L)) * Real.exp (2 * θ * L)) +
                s * C * Real.exp (-(s * L)) := by ring
          _ = s * C * Real.exp (-(s - 2 * θ) * L) + s * C * Real.exp (-s * L) := by
              rw [he]; simp only [neg_mul]
    _ = ENNReal.ofReal (s * C / (s - 2 * θ) + C) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun L => by positivity)]
        congr 1
        rw [integral_add (ia.const_mul _) (ib.const_mul _), integral_const_mul, integral_const_mul,
          integral_exp_mul_Ioi (by linarith) 0, integral_exp_mul_Ioi (by linarith) 0]
        simp only [mul_zero, Real.exp_zero]
        field_simp

/-! ### The endpoint law -/

/-- The log profile of the receiver vanishes on the negative half-line. -/
theorem receiverLogProfile_of_neg (ε : ℝ) {u : ℝ} (hu : u < 0) : receiverLogProfile ε u = 0 := by
  have h0 : receiver ε 0 = 0 := TransHorizonIncidenceMechanics.weightCenteredPrefix_zero _ _
  rw [receiverLogProfile, floor_exp_eq_zero_of_neg hu, h0, mul_zero]

/-- **The endpoint law.** If the receiver at damping `ε` is dominated at `θ` by a finite set `s` of
simple zeros on `Re ρ = θ + ½ + ε` and its energy obeys `E_ε(T) ≤ C (T+1)^{2θ}` for every `T`, then
`Σ_{ρ ∈ s} ‖r_ρ‖² ≤ 2θ C`. -/
theorem residue_mass_le_of_energy_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = θ + 1 / 2 + ε) {C : ℝ}
    (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ (2 * θ)) :
    ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 ≤ 2 * θ * C := by
  set g := receiverLogProfile ε with hg
  have hC : 0 ≤ C := by
    have h0 := hE 0
    rw [← receiver_energy_eq] at h0
    simpa using h0
  have hθ1' : 2 * θ ≤ 1 := by linarith
  have hgm : Measurable g := by
    unfold receiverLogProfile at hg
    rw [hg]
    exact (by fun_prop : Measurable fun u : ℝ => Real.exp (-(u / 2))).mul
      ((measurable_from_nat (f := receiver ε)).comp Real.measurable_exp.nat_floor)
  -- `g²` is integrable on bounded intervals
  have hloc : ∀ L : ℝ, IntegrableOn (fun u => g u ^ 2) (Ioo 0 L) := by
    intro L
    obtain ⟨_, hL2⟩ := receiver_data (ε := ε) hθ one_pos hdom
    have hsq : Integrable (fun u => dampedProfile g (θ + 1) u ^ 2) := hL2.integrable_sq
    refine Integrable.mono' ((hsq.const_mul (Real.exp (2 * (θ + 1) * L))).integrableOn)
      ((hgm.pow_const 2).aestronglyMeasurable) ?_
    refine (ae_restrict_mem measurableSet_Ioo).mono fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), dampedProfile, mul_pow,
      ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    refine le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_exp ?_)
    push_cast
    nlinarith [hu.1, hu.2]
  -- the horizon mass of `g²` is dominated by `C (e^L + 1)^{2θ}`
  have hH : ∀ L, 0 < L → ∫⁻ u in Ioo 0 L, ENNReal.ofReal (g u ^ 2) ≤
      ENNReal.ofReal (C * (Real.exp L + 1) ^ (2 * θ)) := by
    intro L hL
    set T := ⌊Real.exp L⌋₊ with hT
    have hLT : L < Real.log ((T : ℝ) + 1) :=
      (Real.lt_log_iff_exp_lt (by positivity)).mpr (Nat.lt_floor_add_one _)
    have hlog0 : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith [T.cast_nonneg (α := ℝ)])
    calc ∫⁻ u in Ioo 0 L, ENNReal.ofReal (g u ^ 2)
        ≤ ∫⁻ u in Ioo 0 (Real.log ((T : ℝ) + 1)), ENNReal.ofReal (g u ^ 2) :=
          lintegral_mono_set (Ioo_subset_Ioo_right hLT.le)
      _ = ENNReal.ofReal (dampedMobiusEnergy ε T) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hloc _)
            (Eventually.of_forall fun u => sq_nonneg _), receiver_energy_eq_log_integral,
            intervalIntegral.integral_of_le hlog0, integral_Ioc_eq_integral_Ioo]
      _ ≤ ENNReal.ofReal (C * ((T : ℝ) + 1) ^ (2 * θ)) := ENNReal.ofReal_le_ofReal (hE T)
      _ ≤ ENNReal.ofReal (C * (Real.exp L + 1) ^ (2 * θ)) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC)
          exact Real.rpow_le_rpow (by positivity)
            (by linarith [Nat.floor_le (Real.exp_pos L).le]) (by linarith)
  -- the Abel energy is bounded by `(θ + e) C/e + C`
  have hAbel : ∀ e : ℝ, 0 < e → abelGram g (θ + e) 0 0 ≤ (θ + e) * C / e + C := by
    intro e he
    obtain ⟨_, hL2⟩ := receiver_data (ε := ε) hθ he hdom
    have hsq : Integrable (fun u => dampedProfile g (θ + e) u ^ 2) := hL2.integrable_sq
    have hA : abelGram g (θ + e) 0 0 = ∫ u, dampedProfile g (θ + e) u ^ 2 := by
      rw [abelGram_eq_integral_dampedProfile]
      simp only [add_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, sub_zero, sq]
    have hlin := lintegral_exp_mul_le_of_horizon (f := fun u => g u ^ 2)
      (Φ := fun L => C * (Real.exp L + 1) ^ (2 * θ)) (hgm.pow_const 2) (by fun_prop)
      (show 0 < 2 * (θ + e) by linarith) hH
    have hpow := lintegral_exp_mul_power_le (s := 2 * (θ + e)) hθ.le hθ1' (by linarith) hC
    have hlint : ENNReal.ofReal (abelGram g (θ + e) 0 0) =
        ∫⁻ u in Ioi 0, ENNReal.ofReal (Real.exp (-(2 * (θ + e) * u))) *
          ENNReal.ofReal (g u ^ 2) := by
      rw [hA, ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun u => sq_nonneg _),
        setLIntegral_congr Ioi_ae_eq_Ici, ← lintegral_indicator measurableSet_Ici]
      refine lintegral_congr fun u => ?_
      by_cases hu : 0 ≤ u
      · rw [indicator_of_mem (mem_Ici.mpr hu), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          dampedProfile, mul_pow, ← Real.exp_nat_mul]
        congr 3
        push_cast
        ring
      · rw [indicator_of_notMem (by simpa using hu), dampedProfile,
          show g u = 0 from receiverLogProfile_of_neg ε (not_le.mp hu)]
        simp
    have hfin : ENNReal.ofReal (abelGram g (θ + e) 0 0) ≤
        ENNReal.ofReal (2 * (θ + e) * C / (2 * (θ + e) - 2 * θ) + C) :=
      hlint ▸ hlin.trans hpow
    have hnn : 0 ≤ 2 * (θ + e) * C / (2 * (θ + e) - 2 * θ) + C := by
      rw [show 2 * (θ + e) - 2 * θ = 2 * e by ring]; positivity
    rw [ENNReal.ofReal_le_ofReal_iff hnn] at hfin
    calc abelGram g (θ + e) 0 0 ≤ 2 * (θ + e) * C / (2 * (θ + e) - 2 * θ) + C := hfin
      _ = (θ + e) * C / e + C := by
          rw [show 2 * (θ + e) - 2 * θ = 2 * e by ring]
          field_simp
  -- against the capacity law
  by_contra hlt
  simp only [not_le] at hlt
  set R := ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 with hR
  set M := Real.pi * (2 * θ * C + R) / 2 with hM
  have hMlt : M < Real.pi * R := by rw [hM]; have := Real.pi_pos; nlinarith
  have hcap := eventually_le_mul_abelGram_receiver hε hθ hθ1 hdom s hs hMlt
  have hgap : 0 < M - 2 * Real.pi * (θ * C) := by rw [hM]; have := Real.pi_pos; nlinarith
  have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), 2 * Real.pi * (2 * e * C) < M - 2 * Real.pi * (θ * C) := by
    have hc : Tendsto (fun e : ℝ => 2 * Real.pi * (2 * e * C)) (𝓝 0)
        (𝓝 (2 * Real.pi * (2 * 0 * C))) :=
      (by fun_prop : Continuous fun e : ℝ => 2 * Real.pi * (2 * e * C)).tendsto 0
    simp only [mul_zero, zero_mul] at hc
    exact (hc.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hgap)
  obtain ⟨e, he1, he2, he0⟩ := (hcap.and (hsmall.and self_mem_nhdsWithin)).exists
  have he : (0 : ℝ) < e := he0
  have hb := hAbel e he
  have : e * abelGram g (θ + e) 0 0 ≤ (θ + e) * C + e * C := by
    calc e * abelGram g (θ + e) 0 0 ≤ e * ((θ + e) * C / e + C) :=
          mul_le_mul_of_nonneg_left hb he.le
      _ = (θ + e) * C + e * C := by field_simp
  have hpi := Real.pi_pos
  nlinarith

/-- **The endpoint law at the zero abscissa, unconditionally.** For `0 < ε < Θ − ½`, `Θ` the zero
abscissa, put `θ = Θ − ε − ½`. For every finite set `s` of simple zeros of `ζ` on `Re ρ = Θ`, an
energy bound `E_ε(T) ≤ C (T+1)^{2θ}` for all `T` forces `Σ_{ρ ∈ s} ‖r_ρ‖² ≤ 2θ C`. -/
theorem residue_mass_le_of_energy_le_at_zeroAbscissa {ε : ℝ} (hε : 0 < ε)
    (hεΘ : ε < _root_.RHTower.zetaZeroAbscissa - 1 / 2) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = _root_.RHTower.zetaZeroAbscissa) {C : ℝ}
    (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤
      C * ((T : ℝ) + 1) ^ (2 * (_root_.RHTower.zetaZeroAbscissa - ε - 1 / 2))) :
    ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 ≤
      2 * (_root_.RHTower.zetaZeroAbscissa - ε - 1 / 2) * C := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨ρ₀, hρ₀⟩
  · have hC : 0 ≤ C := by
      have h0 := hE 0
      rw [← receiver_energy_eq] at h0
      simpa using h0
    simp only [Finset.sum_empty]
    exact mul_nonneg (by linarith) hC
  set Θ := _root_.RHTower.zetaZeroAbscissa with hΘ
  have hΘ1 : Θ < 1 := by
    obtain ⟨hz, -, hre⟩ := hs ρ₀ hρ₀
    rw [← hre]
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  refine residue_mass_le_of_energy_le hε (by linarith) (by linarith) (fun κ hκ => ?_) s
    (fun ρ hρ => ⟨(hs ρ hρ).1, (hs ρ hρ).2.1, by rw [(hs ρ hρ).2.2]; ring⟩) hE
  exact exists_receiver_energy_le_of_zeroAbscissa hε (by
    rw [max_eq_right (by linarith)]; linarith)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
