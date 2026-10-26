import GaloisForLFunctions.ArithmeticCorrelationGeometry.SubpowerReceiverEnergyTranslatesZeros
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheGaugeMassOfAnEscapeStateIsItsEnergyRatio
import GaloisForLFunctions.ArithmeticDefectRigidity.CommonCofactorLimitsExistAlongPrescribedHorizons
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionExactOrder

/-!
# RH is the visibility of every escape state

Every common limit `L` of the cofactor Grams of the damped Möbius receiver is a finite measure on
the gauge torus (`EscapeStatesAreSpectralMeasuresOnTheGaugeTorus`) of total mass
`gaugeMass L = inf_d d·K_L(d,d)`, squeezed by the energy ratios `E(⌊(T+2)/d⌋)/E(T+1)` along the
horizons of `L` (`TheGaugeMassOfAnEscapeStateIsItsEnergyRatio`).

* **Records make escape states invisible** (`exists_actualCofactorLimit_gaugeMass_eq_zero`). If
  `E(T)/(T+1)^κ` is unbounded for some `κ > 0`, take its record horizons `R`
  (`exists_record_horizons`): `E(M) ≤ E(R)((M+1)/(R+1))^κ` for `M ≤ R`. An actual limit along them
  has `d·K(d,d) ≤ (2/d)^κ` for every `d ≥ 2`, so its gauge mass is zero.
* **The criterion** (`riemannHypothesis_iff_forall_gaugeMass_pos`). RH holds iff at every damping
  `0 < ε < ½` every escape state has positive gauge mass; then every gauge mass equals one
  (`gaugeMass_eq_one_of_riemannHypothesis`). Under RH every damping is admissible and the energy
  is bounded. Conversely, positive mass everywhere forces subpower energy at every damping, which
  translates every off-line zero along an interval of dampings
  (`riemannHypothesis_of_subpower_energy`).

Gauge status: an off-line zero cannot hide in the scale-invariant part of the receiver. It forces
an escape state whose spectral measure on the gauge torus is zero; RH is the statement that the
gauge torus sees every escape state with full mass.
-/

open Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open ArithmeticDefectRigidity ArithmeticContinuationAndCriticalEnergy

/-- **Record horizons.** An unbounded sequence has infinitely many records: indices `R` with
`f M ≤ f R` for every `M ≤ R`. -/
theorem exists_record_horizons {f : ℕ → ℝ} (hf : ¬ BddAbove (Set.range f)) :
    ∃ R : ℕ → ℕ, StrictMono R ∧ ∀ m, ∀ M ≤ R m, f M ≤ f (R m) := by
  have nonempty_range_succ : ∀ {K : ℕ}, (range (K + 1)).Nonempty := fun {K} =>
    ⟨0, mem_range.mpr (Nat.succ_pos K)⟩
  have hrec : ∃ᶠ T in atTop, ∀ M ≤ T, f M ≤ f T := by
    rw [frequently_atTop]
    intro N
    -- some value beyond `N` beats every value up to `N`
    obtain ⟨N', hN'⟩ : ∃ N', (range (N + 1)).sup' nonempty_range_succ f < f N' := by
      by_contra h
      push Not at h
      exact hf ⟨(range (N + 1)).sup' nonempty_range_succ f, by
        rintro _ ⟨n, rfl⟩; exact h n⟩
    obtain ⟨T, hT, hmax⟩ := (range (N' + 1)).exists_max_image f nonempty_range_succ
    refine ⟨T, ?_, fun M hM => hmax M (mem_range.mpr (by
      have := mem_range.mp hT; omega))⟩
    by_contra hlt
    push Not at hlt
    have h1 : f T ≤ (range (N + 1)).sup' nonempty_range_succ f :=
      le_sup' f (mem_range.mpr (by omega))
    have h2 : f N' ≤ f T := hmax N' (mem_range.mpr (by omega))
    linarith
  obtain ⟨R, hR, hrecR⟩ := extraction_of_frequently_atTop hrec
  exact ⟨R, hR, hrecR⟩

/-- **Escape along records is invisible.** If `E(T)/(T+1)^κ` is unbounded for some `κ > 0`, some
actual cofactor limit has gauge mass zero. -/
theorem exists_actualCofactorLimit_gaugeMass_eq_zero {ε : SubcriticalDamping} {κ : ℝ} (hκ : 0 < κ)
    (hunb : ¬ BddAbove (Set.range fun T : ℕ => dampedMobiusEnergy ε T / ((T : ℝ) + 1) ^ κ)) :
    ∃ L : ActualCofactorLimit ε, gaugeMass L.kernel = 0 := by
  obtain ⟨R, hR, hrec⟩ := exists_record_horizons hunb
  -- horizons `T_m = R(m+1) − 1`, so that `T_m + 1 = R(m+1) ≥ 1`
  have hR1 : ∀ m, 1 ≤ R (m + 1) := fun m =>
    Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (hR (Nat.succ_pos m)))
  set Tm : ℕ → ℕ := fun m => R (m + 1) - 1
  have hTm : StrictMono Tm := fun a b hab => by
    have := hR (show a + 1 < b + 1 by omega)
    have h1 := hR1 a; have h2 := hR1 b
    simp only [Tm]; omega
  obtain ⟨ns, hns, L, hL⟩ := exists_actualCofactorLimit_along ε Tm hTm
  refine ⟨L, ?_⟩
  have hsymm := L.kernel_symm
  have hpsd := L.packet_nonneg
  have hcontr := L.packet_dilation_le
  -- `d·K(d,d) ≤ (2/d)^κ` for every `d ≥ 2`
  have hdiag : ∀ d : ℕ+, 2 ≤ (d : ℕ) → (d : ℝ) * L.kernel d d ≤ (2 / (d : ℝ)) ^ κ := by
    intro d hd2
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hdR : ∀ᶠ m in atTop, (d : ℕ) ≤ L.subsequence m + 1 :=
      (ActualCofactorLimitMass.tendsto_subsequence_atTop L).eventually
        (eventually_ge_atTop ((d : ℕ) - 1)) |>.mono fun m hm => by omega
    obtain ⟨m, hm1, hm2⟩ := ((ActualCofactorLimitMass.mul_kernel_le_energyRatio L d hδ).and
      hdR).exists
    -- the horizon `T + 1` is a record
    set T := L.subsequence m
    have hTrec : ∃ k, T + 1 = R k := by
      refine ⟨ns m + 1, ?_⟩
      have : L.subsequence m = Tm (ns m) := by rw [hL]; rfl
      simp only [T, this, Tm]
      have := hR1 (ns m); omega
    obtain ⟨k, hk⟩ := hTrec
    set M := (T + 1 + 1) / (d : ℕ)
    have hMle : M ≤ R k := by
      rw [← hk]
      exact (Nat.div_le_div_left hd2 (by norm_num)).trans (by omega)
    have hrecM := hrec k M hMle
    rw [← hk] at hrecM
    have hE := receiverEnergy_succ_pos ε T
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hT1 : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) + 1 := by positivity
    -- `E(M)/E(T+1) ≤ ((M+1)/(T+2))^κ ≤ (2/d)^κ`
    have hratio : dampedMobiusEnergy ε M / dampedMobiusEnergy ε (T + 1) ≤ (2 / (d : ℝ)) ^ κ := by
      rw [div_le_iff₀ hE]
      have h1 : dampedMobiusEnergy ε M ≤
          dampedMobiusEnergy ε (T + 1) * (((M : ℝ) + 1) / (((T + 1 : ℕ) : ℝ) + 1)) ^ κ := by
        rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hM1 _) (Real.rpow_pos_of_pos hT1 _)] at hrecM
        rw [Real.div_rpow hM1.le hT1.le, mul_div_assoc', le_div_iff₀ (Real.rpow_pos_of_pos hT1 _)]
        linarith
      refine h1.trans ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) ?_ hκ.le) hE.le
      have hd0 : (0 : ℝ) < d := by exact_mod_cast d.pos
      have hMd : (M : ℝ) * d ≤ (T : ℝ) + 2 := by
        have := Nat.div_mul_le_self (T + 1 + 1) d
        exact_mod_cast (by omega : M * (d : ℕ) ≤ T + 2)
      have hdT : (d : ℝ) ≤ (T : ℝ) + 1 := by exact_mod_cast hm2
      rw [div_le_div_iff₀ hT1 hd0]
      push_cast
      nlinarith
    linarith
  -- the infimum over `d` of `(2/d)^κ` is zero
  have hnonneg : 0 ≤ gaugeMass L.kernel := by
    have := asymKernel_psd hsymm hpsd hcontr {1} fun _ => 1
    simpa [gaugeMass] using this
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) hnonneg
  have hlim : Tendsto (fun n : ℕ => (2 / ((n + 2 : ℕ) : ℝ)) ^ κ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 2 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
      exact (this.comp (tendsto_add_atTop_nat 2)).congr fun n => by simp
    have := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.comp h0
    simpa [Function.comp_def, Real.zero_rpow hκ.ne'] using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  rw [ActualCofactorLimitMass.gaugeMass_eq L]
  have hbdd : BddBelow (Set.range fun d : ℕ+ => (d : ℝ) * L.kernel d d) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨d, rfl⟩
    have hd := L.packet_nonneg {d} fun _ => 1
    simp only [sum_singleton, mul_one, one_mul] at hd
    exact mul_nonneg (by positivity) hd
  set d : ℕ+ := ⟨n + 2, by omega⟩
  calc (⨅ d : ℕ+, (d : ℝ) * L.kernel d d) ≤ (d : ℝ) * L.kernel d d := ciInf_le hbdd _
    _ ≤ (2 / (d : ℝ)) ^ κ := hdiag d (by simp [d])
    _ ≤ 0 + δ := by
        have : ((d : ℕ+) : ℝ) = ((n + 2 : ℕ) : ℝ) := rfl
        rw [this]; linarith

/-- Under RH every escape state has gauge mass one. -/
theorem gaugeMass_eq_one_of_riemannHypothesis (hRH : RiemannHypothesis) (ε : SubcriticalDamping)
    (L : ActualCofactorLimit ε) : gaugeMass L.kernel = 1 := by
  have hε : (ε : ℝ) ∈ RHTower.receiverDampings := by
    apply RHTower.Ioi_zetaZeroAbscissa_sub_half_subset_receiverDampings
    rw [Set.mem_Ioi, RHTower.zetaZeroAbscissa_eq_half_of_riemannHypothesis hRH, sub_self]
    exact ε.2.1
  exact ActualCofactorLimitMass.gaugeMass_eq_one_of_admits L
    ((mem_receiverDampings_iff_admits ε.2.1).mp hε)

/-- **RH is the visibility of every escape state.** The Riemann hypothesis holds iff, at every
damping `0 < ε < ½`, every actual common cofactor limit of the damped Möbius receiver has positive
gauge mass (and then every gauge mass is one). -/
theorem riemannHypothesis_iff_forall_gaugeMass_pos :
    RiemannHypothesis ↔ ∀ ε : SubcriticalDamping, ∀ L : ActualCofactorLimit ε,
      0 < gaugeMass L.kernel := by
  constructor
  · intro hRH ε L
    rw [gaugeMass_eq_one_of_riemannHypothesis hRH ε L]
    exact one_pos
  · intro hpos
    refine riemannHypothesis_of_subpower_energy fun ε hε hε2 κ hκ => ?_
    by_contra hno
    set e : SubcriticalDamping := ⟨ε, hε, hε2⟩
    have hunb : ¬ BddAbove (Set.range fun T : ℕ => dampedMobiusEnergy (e : ℝ) T / ((T : ℝ) + 1) ^ κ) := by
      rintro ⟨B, hB⟩
      apply hno
      refine ⟨max B 0, le_max_right _ _, fun T => ?_⟩
      have hpos' : (0 : ℝ) < ((T : ℝ) + 1) ^ κ := Real.rpow_pos_of_pos (by positivity) _
      have h1 := hB ⟨T, rfl⟩
      rw [div_le_iff₀ hpos'] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos'.le)
    obtain ⟨L, hL⟩ := exists_actualCofactorLimit_gaugeMass_eq_zero hκ hunb
    exact (hpos e L).ne' hL

end GaloisForLFunctions.ArithmeticCorrelationGeometry
