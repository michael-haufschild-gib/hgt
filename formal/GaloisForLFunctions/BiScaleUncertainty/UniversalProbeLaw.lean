import GaloisForLFunctions.BiScaleUncertainty.MultiplicitySpectroscopyLaw
import GaloisForLFunctions.HTGeometry.EntireNonzeroPathConnected

/-!
# A generic boost of any source is a universal probe

A source sees a zero `ρ` when `f̂(γ_ρ) ≠ 0`; the packet growth and sign laws only speak about the
zeros a source sees. A **universal probe** sees every zero, so its single packet carries the
information of all compact packets.

The boost `e^{tu} = C_t + S_t` of the hyperbolic multipliers translates the transform:
`(e^{t·}φ)^(z) = φ̂(z − it)`. For each zero the map `t ↦ φ̂(γ_ρ − it)` extends to a nonzero entire
function, so it vanishes for only countably many `t`, and there are countably many zeros:

* `countable_not_seesAllZeros_tilt`: for every nonzero real `φ ∈ C²_c`, all but countably many
  boosts `e^{tu}φ(u)` are universal probes; `exists_universal_tilt` picks one.

For a universal probe `U` (unconditionally):

* `riemannHypothesis_iff_packet_bddAbove_of_universal`: RH iff the single packet `P_U` is eventually
  bounded above (equivalently bounded, or bounded below);
* `xiZeroHalfPlaneBound_iff_packet_upper_of_universal`: every zero has `Re ρ ≤ 1/2 + β` iff
  `P_U ≤ K e^{βτ}` eventually — the zero width is the one-sided growth exponent of one packet;
* `packet_oscillates_of_universal_of_lt`: if a zero has `Re ρ − 1/2 > σ ≥ 0`, then `P_U` exceeds
  `K e^{στ}` and falls below `−K e^{στ}` at arbitrarily large shifts.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- A source sees every zero of `ζ`. -/
def SeesAllZeros (f : ℝ → ℝ) : Prop :=
  ∀ ρ : 𝒵, Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) ≠ 0

/-- The boosted source `e^{tu} φ(u) = (C_t φ + S_t φ)(u)`. -/
def tiltedSource (φ : ℝ → ℝ) (t : ℝ) (u : ℝ) : ℝ := Real.exp (t * u) * φ u

theorem contDiff_tiltedSource {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (t : ℝ) :
    ContDiff ℝ 2 (tiltedSource φ t) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hφ

theorem hasCompactSupport_tiltedSource {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (tiltedSource φ t) :=
  show HasCompactSupport ((fun u => Real.exp (t * u)) * φ) from hφc.mul_left

/-- A boost translates the transform: `(e^{t·}φ)^(z) = φ̂(z − it)`. -/
theorem paperFT_tiltedSource (φ : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    Zeta23.paperFT (fun u => (tiltedSource φ t u : ℂ)) z =
      Zeta23.paperFT (fun u => (φ u : ℂ)) (z - I * t) := by
  unfold Zeta23.paperFT
  congr 1
  funext u
  simp only [tiltedSource]
  push_cast
  rw [mul_comm (cexp _), mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Generic boosts are universal.** For a nonzero real `φ ∈ C²_c`, all but countably many
boosts `e^{tu} φ(u)` see every zero of `ζ`. -/
theorem countable_not_seesAllZeros_tilt {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ0 : φ ≠ 0) :
    {t : ℝ | ¬ SeesAllZeros (tiltedSource φ t)}.Countable := by
  set φ₀ : ℝ → ℂ := fun u => (φ u : ℂ)
  have hφ₀ : Continuous φ₀ := Complex.continuous_ofReal.comp hφ
  have hφ₀c : HasCompactSupport φ₀ := hφc.comp_left Complex.ofReal_zero
  -- the transform does not vanish identically on the real line
  obtain ⟨r, hr⟩ : ∃ r : ℝ, Zeta23.paperFT φ₀ r ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ0
    have h0 := RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_real_eq_zero hφ₀
      (hφ₀.integrable_of_hasCompactSupport hφ₀c) h
    funext u
    simpa [φ₀] using congrFun h0 u
  haveI : Countable 𝒵 := (countable_carrier _).to_subtype
  have hsub : {t : ℝ | ¬ SeesAllZeros (tiltedSource φ t)} ⊆
      ⋃ ρ : 𝒵, (fun t : ℝ => (t : ℂ)) ⁻¹'
        {w : ℂ | Zeta23.paperFT φ₀ (Zeta23.gammaOf ρ - I * w) = 0} := by
    intro t ht
    simp only [SeesAllZeros, not_forall, not_not, mem_setOf_eq] at ht
    obtain ⟨ρ, hρ⟩ := ht
    rw [paperFT_tiltedSource] at hρ
    exact mem_iUnion.mpr ⟨ρ, hρ⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun ρ => ?_)
  refine Set.Countable.preimage ?_ Complex.ofReal_injective
  refine GaloisForLFunctions.HTGeometry.countable_zeros_of_entire_nonzero
    (z := (Zeta23.gammaOf ρ - r) / I) ?_ ?_
  · exact (Zeta23.WeilEF.differentiable_paperFT hφ₀ hφ₀c).comp
      ((differentiable_const _).sub (differentiable_const _ |>.mul differentiable_id))
  · have e : Zeta23.gammaOf ρ - I * ((Zeta23.gammaOf ρ - r) / I) = r := by
      field_simp
      ring
    simpa only [e] using hr

theorem exists_universal_tilt {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : φ ≠ 0) : ∃ t : ℝ, SeesAllZeros (tiltedSource φ t) := by
  by_contra h
  push Not at h
  apply Cardinal.not_countable_real
  exact (countable_not_seesAllZeros_tilt hφ hφc hφ0).mono fun t _ => h t

/-- A zero right of the line exists exactly when RH fails. -/
theorem exists_mem_re_gt_iff_not_riemannHypothesis :
    (∃ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re) ↔ ¬ RiemannHypothesis := by
  refine ⟨fun ⟨ρ, hρ⟩ hRH => ?_, exists_mem_re_gt_of_not_riemannHypothesis⟩
  rw [re_eq_half_of_mem hRH ρ] at hρ
  exact lt_irrefl _ hρ

/-- The zero width in terms of the zeros of `ζ` in the strip. -/
theorem xiZeroHalfPlaneBound_iff_forall_mem {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔ ∀ ρ : 𝒵, (ρ : ℂ).re ≤ 1 / 2 + β := by
  constructor
  · intro hXi ρ
    refine hXi ρ (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
      ⟨ρ.2.1, fun n hn => ?_⟩)
    have h := congrArg Complex.re hn
    have h0 := ρ.2.2.1
    rw [h] at h0
    simp at h0
    linarith [(Nat.cast_nonneg (α := ℝ) n)]
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    have hmem : ρ ∈ 𝒵 := by
      refine ⟨(_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ).1,
        by linarith, ?_⟩
      by_contra h1
      exact _root_.RHTower.xi_ne_zero_of_one_le_re (not_lt.mp h1) hρ
    exact absurd (h ⟨ρ, hmem⟩) (not_le.mpr hlt)

/-- **One packet decides RH.** For a universal probe `U`, RH holds iff its packet is eventually
bounded above. -/
theorem riemannHypothesis_iff_packet_bddAbove_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket U τ ≤ K := by
  have h := packet_upper_iff hU hUc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one, sub_pos] at h
  rw [h]
  constructor
  · intro hRH ρ hρ
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  · intro hblind
    by_contra hRH
    obtain ⟨ρ, hρ⟩ := exists_mem_re_gt_of_not_riemannHypothesis hRH
    exact hsees ρ (hblind ρ hρ)

/-- For a universal probe, RH is also equivalent to boundedness of its packet. -/
theorem riemannHypothesis_iff_packet_bounded_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → |stationaryPacket U τ| ≤ K := by
  rw [riemannHypothesis_iff_packet_bddAbove_of_universal hU hUc hsees]
  exact ⟨fun ⟨T, K, h⟩ => (packet_bounded_iff_blind hU hUc).mpr
      (fun ρ hρ => by
        have h2 := (packet_upper_iff hU hUc le_rfl).mp
          ⟨T, K, fun τ hτ => by simpa using h τ hτ⟩
        exact h2 ρ (by linarith)),
    fun ⟨T, K, h⟩ => ⟨T, K, fun τ hτ => (le_abs_self _).trans (h τ hτ)⟩⟩

/-- **The zero width is the growth exponent of one packet.** For a universal probe `U` and
`β ≥ 0`, every zero has `Re ρ ≤ 1/2 + β` iff `P_U ≤ K e^{βτ}` eventually. -/
theorem xiZeroHalfPlaneBound_iff_packet_upper_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket U τ ≤ K * Real.exp (β * τ) := by
  rw [xiZeroHalfPlaneBound_iff_forall_mem hβ, packet_upper_iff hU hUc hβ]
  constructor
  · intro h ρ hρ
    have := h ρ
    linarith
  · intro h ρ
    by_contra hlt
    push Not at hlt
    exact hsees ρ (h ρ (by linarith))

/-- **Ω± for a universal packet.** If some zero has depth `Re ρ − 1/2 > σ ≥ 0`, the universal
packet exceeds `K e^{στ}` and falls below `−K e^{στ}` at arbitrarily large shifts. -/
theorem packet_oscillates_of_universal_of_lt {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) {σ : ℝ} (hσ : 0 ≤ σ) {ρ : 𝒵}
    (hρ : σ < (ρ : ℂ).re - 1 / 2) (T K : ℝ) :
    (∃ τ, T ≤ τ ∧ K * Real.exp (σ * τ) < stationaryPacket U τ) ∧
      ∃ τ, T ≤ τ ∧ stationaryPacket U τ < -(K * Real.exp (σ * τ)) :=
  packet_oscillates hU hUc hσ hρ (hsees ρ) T K

/-- **Boosted universal probes.** For every nonzero real `φ ∈ C²_c` there is a boost `t` such that
the single packet of `e^{tu}φ(u)` decides RH and has the zero width as its growth exponent. -/
theorem exists_tilt_packet_decides {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : φ ≠ 0) :
    ∃ t : ℝ, (RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        stationaryPacket (tiltedSource φ t) τ ≤ K) ∧
      ∀ β : ℝ, 0 ≤ β → (_root_.RHTower.XiZeroHalfPlaneBound β ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        stationaryPacket (tiltedSource φ t) τ ≤ K * Real.exp (β * τ)) := by
  obtain ⟨t, ht⟩ := exists_universal_tilt hφ.continuous hφc hφ0
  exact ⟨t, riemannHypothesis_iff_packet_bddAbove_of_universal (contDiff_tiltedSource hφ t)
      (hasCompactSupport_tiltedSource hφc t) ht,
    fun β hβ => xiZeroHalfPlaneBound_iff_packet_upper_of_universal (contDiff_tiltedSource hφ t)
      (hasCompactSupport_tiltedSource hφc t) ht hβ⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
