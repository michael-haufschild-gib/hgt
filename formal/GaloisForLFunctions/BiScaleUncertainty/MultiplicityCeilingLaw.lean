import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe

/-!
# The multiplicity ceiling: the optimal packet–Weil constant is the maximal multiplicity

For a real compact `C²` source, the critical packet energy and the critical Weil energy are

`E(f) = Σ_{Re ρ = 1/2} m_ρ² |f̂(γ_ρ)|²`,  `W(f) = Σ_{Re ρ = 1/2} m_ρ |f̂(γ_ρ)|²`,

so `W ≤ E`, with equality for all sources exactly when every critical zero is simple.

**Multiplicity ceiling law** (`multiplicity_ceiling_law`). For every real `K`,

`E(f) ≤ K · W(f)` for every compact `C²` source  ⟺  every critical zero has `m_ρ ≤ K`.

So `sup_f E(f)/W(f)` is the maximal critical multiplicity, and critical multiplicities are
bounded iff `E ≤ K·W` uniformly. The upper bound holds termwise. For the converse, tuned cubic
splines `B(u/R) cos(γ₀u)` have `E/W → m_{ρ₀}` (`tendsto_energy_ratio_tunedSpline`), so one fixed
explicit family reads every multiplicity.

**Prime-side form under RH** (`multiplicity_ceiling_law_of_riemannHypothesis`). Under RH, `E(f)`
is the asymptotic mean square of the packet and `W(f)` is the Weil functional of `h_f`. Hence
every zero has multiplicity at most `K` iff, for every compact `C²` source,

`lim (1/L) ∫_w^L P_f² ≤ K · W(h_f)`.

So the zeta multiplicity bound is one packet-against-Weil inequality.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- **Termwise ceiling.** If every critical multiplicity is at most `K`, then `E(f) ≤ K · W(f)`. -/
theorem criticalPacketEnergy_le_mul_criticalWeilEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℝ}
    (hK : ∀ ρ : criticalZeros, (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) ≤ K) :
    criticalPacketEnergy f ≤ K * criticalWeilEnergy f := by
  set x : criticalZeros → ℝ := fun ρ =>
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2
  set m : criticalZeros → ℝ := fun ρ => (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ)
  have hm1 : ∀ ρ, 1 ≤ m ρ := fun ρ => by
    simp only [m]
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
  have hx0 : ∀ ρ, 0 ≤ x ρ := fun ρ => by positivity
  have hE : Summable fun ρ => m ρ ^ 2 * x ρ := summable_criticalPacketEnergy hf hfc
  have hW : Summable fun ρ => m ρ * x ρ := hE.of_nonneg_of_le
    (fun ρ => mul_nonneg (by linarith [hm1 ρ]) (hx0 ρ))
    fun ρ => mul_le_mul_of_nonneg_right (by nlinarith [hm1 ρ]) (hx0 ρ)
  show ∑' ρ, m ρ ^ 2 * x ρ ≤ K * ∑' ρ, m ρ * x ρ
  rw [← tsum_mul_left]
  refine hE.tsum_le_tsum (fun ρ => ?_) (hW.mul_left K)
  rw [sq, mul_assoc, ← mul_assoc K]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK ρ) (by linarith [hm1 ρ]))
    (hx0 ρ) |>.trans_eq' (by ring)

theorem integral_cubicSpline : ∫ u, cubicSpline u = 1 :=
  RHTower.WeilDeletion.integral_upow one_pos 3

/-- **One explicit family reads every multiplicity**: tuned cubic splines `B(u/R) cos(γ₀u)` have
`E/W → m_{ρ₀}`. -/
theorem tendsto_energy_ratio_tunedSpline (ρ₀ : criticalZeros) :
    Tendsto (fun R : ℝ => criticalPacketEnergy (tunedProbe cubicSpline ((ρ₀ : 𝒵) : ℂ).im R) /
      criticalWeilEnergy (tunedProbe cubicSpline ((ρ₀ : 𝒵) : ℂ).im R)) atTop
        (𝓝 (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ)) :=
  tendsto_energy_ratio_tunedProbe contDiff_cubicSpline hasCompactSupport_cubicSpline
    (by rw [integral_cubicSpline]; exact one_ne_zero) ρ₀

/-- **The ceiling is attained.** A uniform bound `E ≤ K · W` bounds every critical multiplicity
by `K`. -/
theorem mult_le_of_forall_energy_le {K : ℝ}
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      criticalPacketEnergy f ≤ K * criticalWeilEnergy f) (ρ₀ : criticalZeros) :
    (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) ≤ K := by
  have hm1 : (1 : ℝ) ≤ Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) := by
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ₀ : 𝒵).2
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  have hbound : ∀ᶠ R : ℝ in atTop, criticalPacketEnergy (tunedProbe cubicSpline γ₀ R) /
      criticalWeilEnergy (tunedProbe cubicSpline γ₀ R) ≤ max K 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    set f := tunedProbe cubicSpline γ₀ R
    have hEW := h f (contDiff_tunedProbe contDiff_cubicSpline γ₀ R)
      (hasCompactSupport_tunedProbe hasCompactSupport_cubicSpline γ₀ hR)
    have hW0 : 0 ≤ criticalWeilEnergy f := tsum_nonneg fun _ => by positivity
    rcases hW0.eq_or_lt with hW | hW
    · rw [← hW, div_zero]; exact le_max_right _ _
    · rw [div_le_iff₀ hW]
      exact hEW.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW.le)
  have hle := le_of_tendsto (tendsto_energy_ratio_tunedSpline ρ₀) hbound
  rcases le_max_iff.mp hle with h' | h'
  · exact h'
  · linarith

/-- **Multiplicity ceiling law.** `E(f) ≤ K · W(f)` for every compact `C²` source iff every
critical zero has multiplicity at most `K`: the optimal packet–Weil constant is the maximal
critical multiplicity. -/
theorem multiplicity_ceiling_law (K : ℝ) :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      criticalPacketEnergy f ≤ K * criticalWeilEnergy f) ↔
    ∀ ρ : criticalZeros, (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) ≤ K :=
  ⟨mult_le_of_forall_energy_le, fun hK _ hf hfc =>
    criticalPacketEnergy_le_mul_criticalWeilEnergy hf hfc hK⟩

/-- Critical multiplicities are bounded iff the packet energy is uniformly comparable to the
Weil energy. -/
theorem bddAbove_mult_iff :
    (∃ K : ℝ, ∀ ρ : criticalZeros, (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) ≤ K) ↔
      ∃ K : ℝ, ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
        criticalPacketEnergy f ≤ K * criticalWeilEnergy f :=
  exists_congr fun K => (multiplicity_ceiling_law K).symm

/-- **Prime-side ceiling under RH.** Every zero has multiplicity at most `K` iff for every compact
`C²` source the asymptotic mean square of its packet is at most `K` times the Weil functional of
its autocorrelation. -/
theorem multiplicity_ceiling_law_of_riemannHypothesis (hRH : RiemannHypothesis) (K : ℝ) :
    (∀ ρ : 𝒵, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ≤ K) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ w : ℝ, 0 ≤ w →
        (∀ v : ℝ, w < |v| → f v = 0) →
          ∃ E : ℝ, Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket f τ ^ 2) / L) atTop (𝓝 E) ∧
            E ≤ K * (Zeta23.EF.literatureRHS
              (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have hblind : ∀ f : ℝ → ℝ, ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun f ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  constructor
  · intro hK f hf hfc w hw0 hw
    refine ⟨criticalPacketEnergy f,
      tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw0 hw (hblind f), ?_⟩
    rw [literatureRHS_weilTest_of_blind hf hfc (hblind f), ofReal_re]
    exact criticalPacketEnergy_le_mul_criticalWeilEnergy hf hfc fun ρ => hK ρ
  · intro h ρ
    refine mult_le_of_forall_energy_le (fun f hf hfc => ?_) ⟨ρ, re_eq_half_of_mem hRH ρ⟩
    obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
    have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
      hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
    obtain ⟨E, hE, hEK⟩ := h f hf hfc w hw.le hwz
    rw [tendsto_nhds_unique hE
      (tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw.le hwz (hblind f)),
      literatureRHS_weilTest_of_blind hf hfc (hblind f), ofReal_re] at hEK
    exact hEK

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
