import GaloisForLFunctions.HTGeometry.ThetaPluckerFormationOrderIndex
import GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect

/-!
# Integral formation-order charge conservation

For a positive sequence `h` its formation residue is `Res_form(h) = lim e log(h_{e+1}/h_e)`; the
half-density taking a positive law `μ` to `ν` is `S(μ→ν)_e = √(ν_e/μ_e)`.  A positive law is
regular of order `-α` when `e^α h_e = H(1/e)` for large `e`, with a profile `H` differentiable at
`0` and `H(0) ≠ 0`; the half-order charge of two such laws is `q = (α-β)/2`.

* A regular law of order `-α` has `Res_form(h) = -α`, so the order is determined by the law; hence
  `Res_form(S(μ→ν)) = q(μ,ν)`, and charges are antisymmetric and additive, as are the residues of
  half-densities, which multiply pointwise.
* The physical Plücker packet mass and its depth law are regular of order `-6`, with rational
  profiles, and the theta first-exit law is regular of order `-4`.  Hence the formation half-density
  has `Res_form(s) = (6-4)/2 = 1 = -ind(C) = Tr T(1)` on every prime edge.
* Quantitatively `P_{e+1}/P_e = 1 - 6/e + O(e⁻²)`, `π_{e+1}/π_e = 1 - 6/e + O(e⁻²)`,
  `w_{e+1}/w_e = (2e+3)/(2e+11) = 1 - 4/e + O(e⁻²)` and `s_{e+1}/s_e = 1 + 1/e + O(e⁻²)`.
-/

open Filter Topology Set Asymptotics

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource

/-! ## Formation residues -/

/-- **(IFOCC.1).**  `Res_form(h) = r`, i.e. `e log(h_{e+1}/h_e) → r`. -/
def HasFormationResidue (h : ℕ → ℝ) (r : ℝ) : Prop :=
  Tendsto (fun e : ℕ => (e : ℝ) * Real.log (h (e + 1) / h e)) atTop (𝓝 r)

/-- **(IFOCC.2).**  The positive half-density `S(μ→ν)_e = √(ν_e/μ_e)`. -/
def halfDensityTransport (μ ν : ℕ → ℝ) (e : ℕ) : ℝ := Real.sqrt (ν e / μ e)

/-- A law is regular of order `-α`: `e^α h_e = H(1/e)` eventually, with `H` differentiable at `0`
and `H(0) ≠ 0`. -/
def IsRegularDepthLaw (h : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ H : ℝ → ℝ, DifferentiableAt ℝ H 0 ∧ H 0 ≠ 0 ∧
    ∀ᶠ e : ℕ in atTop, (e : ℝ) ^ α * h e = H (e : ℝ)⁻¹

/-- **(IFOCC.3).**  The half-order charge `q = (α - β)/2` of laws of orders `-α` and `-β`. -/
def formationCharge (α β : ℝ) : ℝ := (α - β) / 2

theorem HasFormationResidue.unique {h : ℕ → ℝ} {r t : ℝ} (hr : HasFormationResidue h r)
    (ht : HasFormationResidue h t) : r = t :=
  tendsto_nhds_unique hr ht

/-- `e log((e+1)/e) → 1`. -/
theorem tendsto_natCast_mul_log_succ_div :
    Tendsto (fun e : ℕ => (e : ℝ) * Real.log (((e : ℝ) + 1) / e)) atTop (𝓝 1) := by
  refine ((Real.tendsto_mul_log_one_add_div_atTop 1).comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  simp only [Function.comp]
  congr 2
  field_simp

/-- For `g` differentiable at `0`, `e (g(1/(e+1)) - g(1/e)) → 0`. -/
theorem tendsto_mul_sub_comp_inv_succ {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g 0) :
    Tendsto (fun e : ℕ => (e : ℝ) * (g ((e : ℝ) + 1)⁻¹ - g (e : ℝ)⁻¹)) atTop (𝓝 0) := by
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hg.hasDerivAt)
  have hinv : Tendsto (fun e : ℕ => ((e : ℝ))⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_nhds_zero_nat,
      (eventually_ne_atTop 0).mono fun e he => inv_ne_zero (Nat.cast_ne_zero.mpr he)⟩
  have hφ1 : Tendsto (fun e : ℕ => (e : ℝ) * (g (e : ℝ)⁻¹ - g 0)) atTop (𝓝 (deriv g 0)) :=
    (hslope.comp hinv).congr fun e => by simp [smul_eq_mul]
  have hφ2 : Tendsto (fun e : ℕ => ((e : ℝ) + 1) * (g ((e : ℝ) + 1)⁻¹ - g 0)) atTop
      (𝓝 (deriv g 0)) :=
    (hφ1.comp (tendsto_add_atTop_nat 1)).congr fun e => by simp
  have h := ((tendsto_natCast_div_add_atTop (1 : ℝ)).mul hφ2).sub hφ1
  rw [one_mul, sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (e : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Residue of a regular law.**  A positive regular law of order `-α` has `Res_form = -α`. -/
theorem IsRegularDepthLaw.hasFormationResidue {h : ℕ → ℝ} {α : ℝ} (hpos : ∀ e, 0 < h e)
    (hreg : IsRegularDepthLaw h α) : HasFormationResidue h (-α) := by
  obtain ⟨H, hH, hH0, hev⟩ := hreg
  have hHpos : 0 < H 0 := by
    have hlim : Tendsto (fun e : ℕ => H (e : ℝ)⁻¹) atTop (𝓝 (H 0)) :=
      hH.continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
    have hge : ∀ᶠ e : ℕ in atTop, 0 ≤ H (e : ℝ)⁻¹ := by
      filter_upwards [hev] with e he
      rw [← he]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) α) (hpos e).le
    exact lt_of_le_of_ne (ge_of_tendsto hlim hge) hH0.symm
  have hB := tendsto_mul_sub_comp_inv_succ (hH.log hHpos.ne')
  have hT := (tendsto_natCast_mul_log_succ_div.const_mul (-α)).add hB
  rw [mul_one, add_zero] at hT
  refine hT.congr' ?_
  filter_upwards [hev, (tendsto_add_atTop_nat 1).eventually hev, eventually_ne_atTop 0]
    with e he he1 he0
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he0)
  have he1pos : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  push_cast at he1
  have hH1 : 0 < H ((e : ℝ) + 1)⁻¹ := by
    rw [← he1]
    exact mul_pos (Real.rpow_pos_of_pos he1pos α) (hpos (e + 1))
  have hH2 : 0 < H (e : ℝ)⁻¹ := by
    rw [← he]
    exact mul_pos (Real.rpow_pos_of_pos hepos α) (hpos e)
  have hl1 : Real.log (h (e + 1)) = Real.log (H ((e : ℝ) + 1)⁻¹) - α * Real.log ((e : ℝ) + 1) := by
    rw [← he1, Real.log_mul (Real.rpow_pos_of_pos he1pos α).ne' (hpos (e + 1)).ne',
      Real.log_rpow he1pos]
    ring
  have hl2 : Real.log (h e) = Real.log (H (e : ℝ)⁻¹) - α * Real.log (e : ℝ) := by
    rw [← he, Real.log_mul (Real.rpow_pos_of_pos hepos α).ne' (hpos e).ne', Real.log_rpow hepos]
    ring
  rw [Real.log_div (hpos (e + 1)).ne' (hpos e).ne', hl1, hl2,
    Real.log_div he1pos.ne' hepos.ne']
  ring

/-- The order of a positive regular law is unique. -/
theorem IsRegularDepthLaw.order_unique {h : ℕ → ℝ} {α β : ℝ} (hpos : ∀ e, 0 < h e)
    (hα : IsRegularDepthLaw h α) (hβ : IsRegularDepthLaw h β) : α = β := by
  have := (hα.hasFormationResidue hpos).unique (hβ.hasFormationResidue hpos)
  linarith

/-- Residues of half-densities: `Res_form(S(μ→ν)) = (Res_form ν - Res_form μ)/2`. -/
theorem HasFormationResidue.halfDensityTransport {μ ν : ℕ → ℝ} (hμ : ∀ e, 0 < μ e)
    (hν : ∀ e, 0 < ν e) {r t : ℝ} (h1 : HasFormationResidue μ r) (h2 : HasFormationResidue ν t) :
    HasFormationResidue (halfDensityTransport μ ν) ((t - r) / 2) := by
  unfold HasFormationResidue at *
  refine ((h2.sub h1).div_const 2).congr fun e => ?_
  have hA : 0 < ν (e + 1) / μ (e + 1) := div_pos (hν _) (hμ _)
  have hB : 0 < ν e / μ e := div_pos (hν _) (hμ _)
  simp only [GaloisForLFunctions.HTGeometry.halfDensityTransport]
  rw [Real.log_div (Real.sqrt_pos.2 hA).ne' (Real.sqrt_pos.2 hB).ne', Real.log_sqrt hA.le,
    Real.log_sqrt hB.le, Real.log_div (hν _).ne' (hμ _).ne', Real.log_div (hν _).ne' (hμ _).ne',
    Real.log_div (hν _).ne' (hν _).ne', Real.log_div (hμ _).ne' (hμ _).ne']
  ring

/-- Residues add under pointwise products of positive sequences. -/
theorem HasFormationResidue.mul {f g : ℕ → ℝ} (hf0 : ∀ e, 0 < f e) (hg0 : ∀ e, 0 < g e)
    {r t : ℝ} (hf : HasFormationResidue f r) (hg : HasFormationResidue g t) :
    HasFormationResidue (fun e => f e * g e) (r + t) := by
  unfold HasFormationResidue at *
  refine (hf.add hg).congr fun e => ?_
  rw [mul_div_mul_comm, Real.log_mul (div_pos (hf0 _) (hf0 _)).ne' (div_pos (hg0 _) (hg0 _)).ne']
  ring

/-- Residues change sign under pointwise inversion. -/
theorem HasFormationResidue.inv {f : ℕ → ℝ} (hf0 : ∀ e, 0 < f e) {r : ℝ}
    (hf : HasFormationResidue f r) : HasFormationResidue (fun e => (f e)⁻¹) (-r) := by
  unfold HasFormationResidue at *
  refine hf.neg.congr fun e => ?_
  rw [inv_div_inv, Real.log_div (hf0 e).ne' (hf0 _).ne', Real.log_div (hf0 _).ne' (hf0 e).ne']
  ring

/-- Half-densities compose: `S(μ→ω) = S(ν→ω) S(μ→ν)`. -/
theorem halfDensityTransport_mul {μ ν ω : ℕ → ℝ} (hμ : ∀ e, 0 < μ e) (hν : ∀ e, 0 < ν e)
    (hω : ∀ e, 0 < ω e) (e : ℕ) :
    halfDensityTransport μ ω e = halfDensityTransport ν ω e * halfDensityTransport μ ν e := by
  unfold halfDensityTransport
  rw [← Real.sqrt_mul (div_pos (hω e) (hν e)).le]
  congr 1
  field_simp [(hν e).ne', (hμ e).ne']

/-- Half-densities invert: `S(ν→μ) = S(μ→ν)⁻¹`. -/
theorem halfDensityTransport_swap (μ ν : ℕ → ℝ) (e : ℕ) :
    halfDensityTransport ν μ e = (halfDensityTransport μ ν e)⁻¹ := by
  unfold halfDensityTransport
  rw [← Real.sqrt_inv, inv_div]

theorem halfDensityTransport_pos {μ ν : ℕ → ℝ} (hμ : ∀ e, 0 < μ e) (hν : ∀ e, 0 < ν e) (e : ℕ) :
    0 < halfDensityTransport μ ν e :=
  Real.sqrt_pos.2 (div_pos (hν e) (hμ e))

/-- **Charge law.**  For positive regular laws of orders `-α` and `-β`,
`Res_form(S(μ→ν)) = q(μ,ν) = (α-β)/2`. -/
theorem hasFormationResidue_halfDensityTransport {μ ν : ℕ → ℝ} {α β : ℝ} (hμ : ∀ e, 0 < μ e)
    (hν : ∀ e, 0 < ν e) (hα : IsRegularDepthLaw μ α) (hβ : IsRegularDepthLaw ν β) :
    HasFormationResidue (halfDensityTransport μ ν) (formationCharge α β) := by
  have h := (hα.hasFormationResidue hμ).halfDensityTransport hμ hν (hβ.hasFormationResidue hν)
  have heq : (-β - -α) / 2 = formationCharge α β := by unfold formationCharge; ring
  rwa [heq] at h

/-- **(IFOCC.5).**  Charges are antisymmetric and additive, and so are the residues of the
corresponding half-densities. -/
theorem formationCharge_antisymm_add {μ ν ω : ℕ → ℝ} {α β γ : ℝ} (hμ : ∀ e, 0 < μ e)
    (hν : ∀ e, 0 < ν e) (hω : ∀ e, 0 < ω e) (hα : IsRegularDepthLaw μ α)
    (hβ : IsRegularDepthLaw ν β) (hγ : IsRegularDepthLaw ω γ) :
    formationCharge α β = -formationCharge β α ∧
      formationCharge α γ = formationCharge α β + formationCharge β γ ∧
      HasFormationResidue (halfDensityTransport ν μ) (-formationCharge α β) ∧
      HasFormationResidue (halfDensityTransport μ ω)
        (formationCharge α β + formationCharge β γ) := by
  refine ⟨by unfold formationCharge; ring, by unfold formationCharge; ring, ?_, ?_⟩
  · have h := (hasFormationResidue_halfDensityTransport hμ hν hα hβ).inv
      (halfDensityTransport_pos hμ hν)
    refine (show (fun e => (halfDensityTransport μ ν e)⁻¹) = halfDensityTransport ν μ from
      funext fun e => (halfDensityTransport_swap μ ν e).symm) ▸ h
  · have h := (hasFormationResidue_halfDensityTransport hν hω hβ hγ).mul
      (halfDensityTransport_pos hν hω) (halfDensityTransport_pos hμ hν)
      (hasFormationResidue_halfDensityTransport hμ hν hα hβ)
    rw [add_comm]
    refine (show (fun e => halfDensityTransport ν ω e * halfDensityTransport μ ν e) =
      halfDensityTransport μ ω from
      funext fun e => (halfDensityTransport_mul hμ hν hω e).symm) ▸ h

/-! ## Rational profiles of the physical and theta laws -/

/-- The profile of one scaled Cauchy–Plücker minor, `e⁶ R(e) = G(1/e)`. -/
def pluckerMinorProfile (a α β A B t : ℝ) : ℝ :=
  (2 * a * ((A - B) + (α * A - β * B) * t)) ^ 2 /
    (((A + α * A * t) ^ 2 - a ^ 2 * t ^ 2) * ((B + β * B * t) ^ 2 - a ^ 2 * t ^ 2)) ^ 2

theorem pow_six_mul_pluckerSq_eq_profile (a α β A B : ℝ) {e : ℝ} (he : e ≠ 0) :
    e ^ 6 * twoBoundaryCauchyPairPluckerSq a ((e + α) * A) ((e + β) * B) =
      pluckerMinorProfile a α β A B e⁻¹ := by
  rw [pow_six_mul_twoBoundaryCauchyPairPluckerSq he, pluckerMinorProfile]
  have e1 : (A - B) + (α * A - β * B) * e⁻¹ = ((e + α) * A - (e + β) * B) / e := by
    field_simp
    ring
  have e2 : ∀ γ C : ℝ, (C + γ * C * e⁻¹) ^ 2 - a ^ 2 * e⁻¹ ^ 2 =
      (((e + γ) * C) ^ 2 - a ^ 2) / e ^ 2 := by
    intro γ C
    field_simp
  rw [e1, e2 α A, e2 β B]

theorem contDiffAt_pluckerMinorProfile (a α β : ℝ) {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    ContDiffAt ℝ 1 (pluckerMinorProfile a α β A B) 0 := by
  have hden : (((A + α * A * 0) ^ 2 - a ^ 2 * 0 ^ 2) * ((B + β * B * 0) ^ 2 - a ^ 2 * 0 ^ 2)) ^ 2
      ≠ 0 := by
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero]
    exact pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB))
  exact ContDiffAt.div (f := fun t => (2 * a * ((A - B) + (α * A - β * B) * t)) ^ 2)
    (g := fun t => (((A + α * A * t) ^ 2 - a ^ 2 * t ^ 2) *
      ((B + β * B * t) ^ 2 - a ^ 2 * t ^ 2)) ^ 2) (by fun_prop) (by fun_prop) hden

section Profiles

variable (p q : Nat.Primes)

/-- The rational profile `H` of the physical packet: `e⁶ P_e = H(1/e)`. -/
def pluckerPartitionProfile (t : ℝ) : ℝ :=
  pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture (1 / 2) (3 / 2) (Real.log p)
      (Real.log p) t *
      (gammaSewnMobiusApertureBoundaryAmplitude p *
        gammaSewnMobiusApertureBoundaryAmplitude p) ^ 2 +
    pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture (1 / 2) (1 / 2) (Real.log p)
      (Real.log q) t *
      (gammaSewnMobiusApertureBoundaryAmplitude p *
        gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
    pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture (1 / 2) (3 / 2) (Real.log p)
      (Real.log q) t *
      (gammaSewnMobiusApertureBoundaryAmplitude p *
        gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
    pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture (3 / 2) (1 / 2) (Real.log p)
      (Real.log q) t *
      (gammaSewnMobiusApertureBoundaryAmplitude p *
        gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
    pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture (3 / 2) (3 / 2) (Real.log p)
      (Real.log q) t *
      (gammaSewnMobiusApertureBoundaryAmplitude p *
        gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
    pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture (1 / 2) (3 / 2) (Real.log q)
      (Real.log q) t *
      (gammaSewnMobiusApertureBoundaryAmplitude q *
        gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2

theorem pow_six_mul_partition_eq_profile {e : ℕ} (he : e ≠ 0) :
    (e : ℝ) ^ 6 * gammaSewnCriticalPrimeDepthPacket_Partition e p q =
      pluckerPartitionProfile p q (e : ℝ)⁻¹ := by
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  rw [gammaSewnCriticalPrimeDepthPacket_Partition_eq, pluckerPartitionProfile]
  simp only [mul_add, ← mul_assoc, pow_six_mul_pluckerSq_eq_profile _ _ _ _ _ he']

theorem contDiffAt_pluckerPartitionProfile : ContDiffAt ℝ 1 (pluckerPartitionProfile p q) 0 := by
  have hL := (log_natPrimes_pos p).ne'
  have hM := (log_natPrimes_pos q).ne'
  unfold pluckerPartitionProfile
  have t := fun (α β A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) =>
    contDiffAt_pluckerMinorProfile gammaSewnCriticalFinitePacket_aperture α β hA hB
  exact (((((t _ _ _ _ hL hL).mul contDiffAt_const).add
    ((t _ _ _ _ hL hM).mul contDiffAt_const)).add ((t _ _ _ _ hL hM).mul contDiffAt_const)).add
    ((t _ _ _ _ hL hM).mul contDiffAt_const)).add ((t _ _ _ _ hL hM).mul contDiffAt_const) |>.add
    ((t _ _ _ _ hM hM).mul contDiffAt_const)

theorem pluckerPartitionProfile_zero :
    pluckerPartitionProfile p q 0 = pluckerOrderConstant p q := by
  have hcont : Tendsto (fun e : ℕ => pluckerPartitionProfile p q (e : ℝ)⁻¹) atTop
      (𝓝 (pluckerPartitionProfile p q 0)) :=
    (contDiffAt_pluckerPartitionProfile p q).continuousAt.tendsto.comp
      tendsto_inv_atTop_nhds_zero_nat
  refine tendsto_nhds_unique hcont
    ((tendsto_pow_six_mul_gammaSewnCriticalPrimeDepthPacket_Partition p q).congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with e he
  exact pow_six_mul_partition_eq_profile p q he

/-- The rational profile of the theta first-exit law: `e⁴ w_e = W(1/e)`. -/
def thetaExitProfile (t : ℝ) : ℝ := 630 / ((2 + 3 * t) * (2 + 5 * t) * (2 + 7 * t) * (2 + 9 * t))

omit p q in
theorem pow_four_mul_thetaFlux_eq_profile {e : ℕ} (he : e ≠ 0) :
    (e : ℝ) ^ 4 * thetaCuspMellinSixFlux e = thetaExitProfile (e : ℝ)⁻¹ := by
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  rw [thetaCuspMellinSixFlux_eq, thetaExitProfile]
  push_cast
  field_simp

omit p q in
theorem contDiffAt_thetaExitProfile : ContDiffAt ℝ 1 thetaExitProfile 0 := by
  unfold thetaExitProfile
  exact ContDiffAt.div (f := fun _ => (630 : ℝ))
    (g := fun t => (2 + 3 * t) * (2 + 5 * t) * (2 + 7 * t) * (2 + 9 * t)) contDiffAt_const
    (by fun_prop) (by norm_num)

omit p q in
theorem thetaExitProfile_zero : thetaExitProfile 0 = 315 / 8 := by
  norm_num [thetaExitProfile]

/-- The physical packet mass is regular of order `-6`. -/
theorem isRegularDepthLaw_partition {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    IsRegularDepthLaw (fun e => gammaSewnCriticalPrimeDepthPacket_Partition e p q) 6 := by
  refine ⟨pluckerPartitionProfile p q,
    (contDiffAt_pluckerPartitionProfile p q).differentiableAt one_ne_zero, ?_, ?_⟩
  · rw [pluckerPartitionProfile_zero]
    exact (pluckerOrderConstant_pos hpq).ne'
  · filter_upwards [eventually_ne_atTop 0] with e he
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_six_mul_partition_eq_profile p q he

/-- The physical depth law is regular of order `-6`. -/
theorem isRegularDepthLaw_pluckerDepthLaw {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    IsRegularDepthLaw (pluckerDepthLaw p q) 6 := by
  refine ⟨fun t => pluckerFisherClock p q / pluckerDepthTotal p q * pluckerPartitionProfile p q t,
    (differentiableAt_const _).mul
      ((contDiffAt_pluckerPartitionProfile p q).differentiableAt one_ne_zero), ?_, ?_⟩
  · show pluckerFisherClock p q / pluckerDepthTotal p q * pluckerPartitionProfile p q 0 ≠ 0
    rw [pluckerPartitionProfile_zero]
    exact mul_ne_zero (div_pos (pluckerFisherClock_pos p q) (pluckerDepthTotal_pos hpq)).ne'
      (pluckerOrderConstant_pos hpq).ne'
  · filter_upwards [eventually_ne_atTop 0] with e he
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ←
      pow_six_mul_partition_eq_profile p q he, pluckerDepthLaw, pluckerDepthWeight_eq]
    ring

/-- The theta first-exit law is regular of order `-4`. -/
theorem isRegularDepthLaw_thetaCuspMellinSixFlux :
    IsRegularDepthLaw thetaCuspMellinSixFlux 4 := by
  refine ⟨thetaExitProfile, contDiffAt_thetaExitProfile.differentiableAt one_ne_zero, ?_, ?_⟩
  · rw [thetaExitProfile_zero]
    norm_num
  · filter_upwards [eventually_ne_atTop 0] with e he
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_four_mul_thetaFlux_eq_profile he

end Profiles

/-! ## The conservation identity -/

theorem formationHalfDensity_eq_halfDensityTransport (p q : Nat.Primes) :
    formationHalfDensity p q = halfDensityTransport (pluckerDepthLaw p q) thetaCuspMellinSixFlux :=
  rfl

/-- **(IFOCC.4), first equalities.**  `Res_form(s) = q(π, w) = (6-4)/2 = 1`. -/
theorem hasFormationResidue_formationHalfDensity {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    HasFormationResidue (formationHalfDensity p q) (formationCharge 6 4) ∧
      formationCharge 6 4 = 1 := by
  refine ⟨?_, by norm_num [formationCharge]⟩
  rw [formationHalfDensity_eq_halfDensityTransport]
  exact hasFormationResidue_halfDensityTransport (pluckerDepthLaw_pos hpq)
    thetaCuspMellinSixFlux_pos (isRegularDepthLaw_pluckerDepthLaw hpq)
    isRegularDepthLaw_thetaCuspMellinSixFlux

/-! ## Quantitative ratio laws -/

/-- **(IFOCC, (3)).**  `w_{e+1}/w_e = (2e+3)/(2e+11)`. -/
theorem thetaCuspMellinSixFlux_succ_div (e : ℕ) :
    thetaCuspMellinSixFlux (e + 1) / thetaCuspMellinSixFlux e =
      (2 * (e : ℝ) + 3) / (2 * e + 11) := by
  rw [thetaCuspMellinSixFlux_eq, thetaCuspMellinSixFlux_eq]
  push_cast
  field_simp
  ring

/-- For a profile `C¹` at `0` with `R(0) > 0`, `R(1/(e+1))/R(1/e) = 1 + O(e⁻²)`. -/
theorem isBigO_profile_ratio_sub_one {R : ℝ → ℝ} (hR : ContDiffAt ℝ 1 R 0) (hR0 : 0 < R 0) :
    (fun e : ℕ => R ((e : ℝ) + 1)⁻¹ / R (e : ℝ)⁻¹ - 1) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  obtain ⟨K, U, hU, hLip⟩ := hR.exists_lipschitzOnWith
  have hinv : Tendsto (fun e : ℕ => ((e : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hinv1 : Tendsto (fun e : ℕ => ((e : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (hinv.comp (tendsto_add_atTop_nat 1)).congr fun e => by simp
  have hRlim : Tendsto (fun e : ℕ => R (e : ℝ)⁻¹) atTop (𝓝 (R 0)) :=
    hR.continuousAt.tendsto.comp hinv
  refine IsBigO.of_bound (2 * K / R 0) ?_
  filter_upwards [hinv.eventually hU, hinv1.eventually hU,
    hRlim.eventually (lt_mem_nhds (half_lt_self hR0)), eventually_ne_atTop 0]
    with e h1 h2 h3 he
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hRe : 0 < R (e : ℝ)⁻¹ := lt_trans (half_pos hR0) h3
  have hdist := hLip.dist_le_mul _ h2 _ h1
  rw [Real.dist_eq, Real.dist_eq] at hdist
  have hgap : |((e : ℝ) + 1)⁻¹ - (e : ℝ)⁻¹| ≤ ((e : ℝ) ^ 2)⁻¹ := by
    rw [abs_sub_comm, abs_of_nonneg (by
      rw [sub_nonneg]; exact inv_anti₀ hepos (by linarith))]
    rw [inv_sub_inv hepos.ne' (by positivity), div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((e : ℝ) ^ 2)⁻¹),
    div_sub_one hRe.ne', abs_div, abs_of_pos hRe, div_le_iff₀ hRe]
  calc |R ((e : ℝ) + 1)⁻¹ - R (e : ℝ)⁻¹| ≤ K * ((e : ℝ) ^ 2)⁻¹ :=
        hdist.trans (mul_le_mul_of_nonneg_left hgap K.2)
    _ ≤ 2 * K / R 0 * ((e : ℝ) ^ 2)⁻¹ * R (e : ℝ)⁻¹ := by
        have hK := K.2
        have : (K : ℝ) ≤ 2 * K / R 0 * R (e : ℝ)⁻¹ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hR0]
          nlinarith
        nlinarith [inv_nonneg.2 (sq_nonneg (e : ℝ))]

/-- `(e/(e+1))⁶ = 1 - 6/e + O(e⁻²)`. -/
theorem isBigO_div_succ_pow_six_sub :
    (fun e : ℕ => ((e : ℝ) / ((e : ℝ) + 1)) ^ 6 - (1 - 6 / (e : ℝ))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  refine IsBigO.of_bound 321 ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have he1 : (1 : ℝ) ≤ e := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero he)
  have hid : ((e : ℝ) / ((e : ℝ) + 1)) ^ 6 - (1 - 6 / (e : ℝ)) =
      (21 * (e : ℝ) ^ 5 + 70 * e ^ 4 + 105 * e ^ 3 + 84 * e ^ 2 + 35 * e + 6) /
        ((e : ℝ) * ((e : ℝ) + 1) ^ 6) := by
    field_simp
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hid, abs_of_pos (by positivity),
    abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  rw [show 321 * ((e : ℝ) ^ 2)⁻¹ * ((e : ℝ) * ((e : ℝ) + 1) ^ 6) =
    321 * ((e : ℝ) + 1) ^ 6 / e by field_simp, le_div_iff₀ hepos]
  have h0 : (0 : ℝ) ≤ e := hepos.le
  nlinarith [pow_le_pow_left₀ h0 (le_add_of_nonneg_right zero_le_one : (e : ℝ) ≤ e + 1) 6,
    pow_pos hepos 2, pow_pos hepos 3, pow_pos hepos 4, pow_pos hepos 5, pow_pos hepos 6]

/-- **(IFOCC, (1)).**  `P_{e+1}/P_e = 1 - 6/e + O(e⁻²)`. -/
theorem isBigO_partition_ratio {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (fun e : ℕ => gammaSewnCriticalPrimeDepthPacket_Partition (e + 1) p q /
        gammaSewnCriticalPrimeDepthPacket_Partition e p q - (1 - 6 / (e : ℝ))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  have hK : 0 < pluckerPartitionProfile p q 0 := by
    rw [pluckerPartitionProfile_zero]
    exact pluckerOrderConstant_pos hpq
  have hρ := isBigO_profile_ratio_sub_one (contDiffAt_pluckerPartitionProfile p q) hK
  have hpow := isBigO_div_succ_pow_six_sub
  have hbdd : (fun e : ℕ => ((e : ℝ) / ((e : ℝ) + 1)) ^ 6) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (by positivity) (div_le_one_of_le₀ (by linarith) (by positivity)))
  have hsum := hpow.add ((hbdd.mul hρ).trans (by simp only [one_mul]; exact isBigO_refl _ _))
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with e he
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hP : ∀ k : ℕ, k ≠ 0 → gammaSewnCriticalPrimeDepthPacket_Partition k p q =
      pluckerPartitionProfile p q (k : ℝ)⁻¹ / (k : ℝ) ^ 6 := fun k hk => by
    rw [← pow_six_mul_partition_eq_profile p q hk]
    field_simp
  have hR0 : pluckerPartitionProfile p q (e : ℝ)⁻¹ ≠ 0 := by
    rw [← pow_six_mul_partition_eq_profile p q he]
    exact mul_ne_zero (pow_ne_zero 6 hepos.ne')
      (gammaSewnCriticalPrimeDepthPacket_Partition_pos hpq).ne'
  rw [hP e he, hP (e + 1) (Nat.succ_ne_zero e)]
  push_cast
  field_simp
  ring

/-- **(IFOCC, (2)).**  `π_{e+1}/π_e = 1 - 6/e + O(e⁻²)`. -/
theorem isBigO_pluckerDepthLaw_ratio {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (fun e : ℕ => pluckerDepthLaw p q (e + 1) / pluckerDepthLaw p q e - (1 - 6 / (e : ℝ)))
      =O[atTop] (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  refine (isBigO_partition_ratio hpq).congr' (Eventually.of_forall fun e => ?_)
    (EventuallyEq.refl _ _)
  have hF := (pluckerFisherClock_pos p q).ne'
  have hZ := (pluckerDepthTotal_pos hpq).ne'
  simp only [pluckerDepthLaw, pluckerDepthWeight_eq]
  field_simp

/-- **(IFOCC, (3)).**  `w_{e+1}/w_e = 1 - 4/e + O(e⁻²)`. -/
theorem isBigO_thetaCuspMellinSixFlux_ratio :
    (fun e : ℕ => thetaCuspMellinSixFlux (e + 1) / thetaCuspMellinSixFlux e - (1 - 4 / (e : ℝ)))
      =O[atTop] (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  refine IsBigO.of_bound 22 ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  rw [thetaCuspMellinSixFlux_succ_div, Real.norm_eq_abs, Real.norm_eq_abs,
    show (2 * (e : ℝ) + 3) / (2 * e + 11) - (1 - 4 / (e : ℝ)) = 44 / ((e : ℝ) * (2 * e + 11)) by
      field_simp
      ring,
    abs_of_pos (by positivity), abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  rw [show 22 * ((e : ℝ) ^ 2)⁻¹ * ((e : ℝ) * (2 * e + 11)) = 22 * (2 * e + 11) / e by
    field_simp, le_div_iff₀ hepos]
  nlinarith

/-- **(IFOCC, (4)).**  `s_{e+1}/s_e = 1 + 1/e + O(e⁻²)`: the universal unit logarithmic shift. -/
theorem isBigO_formationHalfDensity_ratio {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (fun e : ℕ => formationHalfDensity p q (e + 1) / formationHalfDensity p q e -
        (1 + 1 / (e : ℝ))) =O[atTop] (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  set c := pluckerFisherClock p q / pluckerDepthTotal p q
  have hc : 0 < c := div_pos (pluckerFisherClock_pos p q) (pluckerDepthTotal_pos hpq)
  set R : ℝ → ℝ := fun t => Real.sqrt (thetaExitProfile t / (c * pluckerPartitionProfile p q t))
  have hP0 : 0 < pluckerPartitionProfile p q 0 := by
    rw [pluckerPartitionProfile_zero]
    exact pluckerOrderConstant_pos hpq
  have hin : 0 < thetaExitProfile 0 / (c * pluckerPartitionProfile p q 0) :=
    div_pos (by rw [thetaExitProfile_zero]; norm_num) (mul_pos hc hP0)
  have hR0 : 0 < R 0 := Real.sqrt_pos.2 hin
  have hRc : ContDiffAt ℝ 1 R 0 :=
    (contDiffAt_thetaExitProfile.div (contDiffAt_const.mul
      (contDiffAt_pluckerPartitionProfile p q)) (mul_pos hc hP0).ne').sqrt hin.ne'
  have hRpos : ∀ k : ℕ, k ≠ 0 → 0 < R (k : ℝ)⁻¹ := fun k hk => by
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    refine Real.sqrt_pos.2 ?_
    rw [← pow_four_mul_thetaFlux_eq_profile hk, ← pow_six_mul_partition_eq_profile p q hk]
    exact div_pos (mul_pos (pow_pos hkpos 4) (thetaCuspMellinSixFlux_pos k))
      (mul_pos hc (mul_pos (pow_pos hkpos 6) (gammaSewnCriticalPrimeDepthPacket_Partition_pos hpq)))
  have hs : ∀ k : ℕ, k ≠ 0 → formationHalfDensity p q k = (k : ℝ) * R (k : ℝ)⁻¹ := fun k hk => by
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hP := (gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := k) hpq).ne'
    have hkR : (k : ℝ) * R (k : ℝ)⁻¹ = Real.sqrt ((k : ℝ) ^ 2 *
        (thetaExitProfile (k : ℝ)⁻¹ / (c * pluckerPartitionProfile p q (k : ℝ)⁻¹))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hkpos.le]
    rw [hkR, formationHalfDensity, ← pow_four_mul_thetaFlux_eq_profile hk,
      ← pow_six_mul_partition_eq_profile p q hk]
    congr 1
    simp only [c, pluckerDepthLaw, pluckerDepthWeight_eq]
    field_simp
  have hρ := isBigO_profile_ratio_sub_one hRc hR0
  have hbdd : (fun e : ℕ => 1 + 1 / (e : ℝ)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    IsBigO.of_bound 2 (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one, abs_of_nonneg (by positivity)]
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h
        norm_num
      · have : (1 : ℝ) ≤ e := Nat.one_le_cast.mpr h
        have : 1 / (e : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
        linarith)
  refine ((hbdd.mul hρ).trans (by simp only [one_mul]; exact isBigO_refl _ _)).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with e he
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hR1 := hRpos e he
  rw [hs e he, hs (e + 1) (Nat.succ_ne_zero e)]
  push_cast
  field_simp

/-! ## Integral formation-order charge conservation -/

/-- **Theorem IFOCC.**  On every prime edge `p < q`, the formation half-density has
`Res_form(s) = q(π, w) = (6-4)/2 = 1 = -ind(C) = Tr T(1)`; the depth laws have orders `-6` and
`-4`; and `s_{e+1}/s_e = 1 + 1/e + O(e⁻²)`. -/
theorem integral_formation_order_charge_conservation {p q : Nat.Primes}
    (hpq : (p : ℕ) < (q : ℕ)) :
    IsRegularDepthLaw (pluckerDepthLaw p q) 6 ∧
    IsRegularDepthLaw thetaCuspMellinSixFlux 4 ∧
    HasFormationResidue (formationHalfDensity p q) (formationCharge 6 4) ∧
    formationCharge 6 4 = 1 ∧
    ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) = 1 ∧
    ContinuousLinearMap.opTrace (primeHodgeHistoryIntegralNuclearHomotopyDefect 1) = 1 ∧
    (fun e : ℕ => formationHalfDensity p q (e + 1) / formationHalfDensity p q e -
        (1 + 1 / (e : ℝ))) =O[atTop] (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  obtain ⟨hres, hq⟩ := hasFormationResidue_formationHalfDensity hpq
  refine ⟨isRegularDepthLaw_pluckerDepthLaw hpq, isRegularDepthLaw_thetaCuspMellinSixFlux, hres,
    hq, ?_, ?_, isBigO_formationHalfDensity_ratio hpq⟩
  · rw [primeHodgeHistorySurvivalShiftIndex_eq_neg_one]
    norm_num
  · rw [primeHodgeHistoryIntegralNuclearHomotopyDefect_one]
    exact primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1

end GaloisForLFunctions.HTGeometry
