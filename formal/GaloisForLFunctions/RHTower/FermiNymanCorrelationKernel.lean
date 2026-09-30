import GaloisForLFunctions.RHTower.FermiNymanMultiplicityIndex

/-!
# Exact bounded kernel of the Fermi multiplicity coordinates

Vanishing correlation jets force dyadic self-similarity by local pole cancellation. Conversely,
continuous self-similarity gives boundedness on `(0,1]`: each point reduces dyadically to the
compact fundamental interval `[1/2,1]`. A bounded witness has Mellin exponent zero, so its literal
source correlation factors as zeta times an analytic function near every right-strip zero.
Consequently every submultiplicity correlation jet vanishes.

The intrinsic kernel set therefore equals the actual bounded witness set, without a Riemann
hypothesis or finiteness premise. The kernel is neutral; it is not identified with the form radical.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem dyadicSelfSimilar_mul_pow_half {w : ℝ → ℂ}
    (hs : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t * (1 / 2 : ℝ) ^ n) = w t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp0 : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    have hp1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hx : t * (1 / 2 : ℝ) ^ n ∈ Ioc (0 : ℝ) 1 :=
      ⟨mul_pos ht.1 hp0, by nlinarith [ht.2]⟩
    rw [pow_succ, show t * ((1 / 2 : ℝ) ^ n * (1 / 2)) =
      (t * (1 / 2 : ℝ) ^ n) / 2 by ring, hs _ hx, ih]

theorem bounded_of_continuous_dyadicSelfSimilar {w : ℝ → ℂ}
    (hc : ContinuousOn w (Ioc (0 : ℝ) 1))
    (hs : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t) :
    ∃ M : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M := by
  have hcont : ContinuousOn w (Icc (1 / 2 : ℝ) 1) := hc.mono (by
    intro t ht
    exact ⟨lt_of_lt_of_le (by norm_num) ht.1, ht.2⟩)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨M, fun t ht => ?_⟩
  obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near_of_lt_one ht.1 ht.2
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  let x := t / (1 / 2 : ℝ) ^ n
  have hx0 : 1 / 2 < x := by
    apply (lt_div_iff₀ hp).mpr
    rw [pow_succ] at hn0
    nlinarith
  have hx1 : x ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hn1)
  have heq : x * (1 / 2 : ℝ) ^ n = t := div_mul_cancel₀ t hp.ne'
  calc
    ‖w t‖ = ‖w (x * (1 / 2 : ℝ) ^ n)‖ := by rw [heq]
    _ = ‖w x‖ := congrArg norm (dyadicSelfSimilar_mul_pow_half hs n
      ⟨by linarith, hx1⟩)
    _ ≤ M := hM x ⟨hx0.le, hx1⟩

theorem IsMellinFermiWitness.analyticAt_witnessMellin {w : ℝ → ℂ} {a : ℝ}
    (hw : IsMellinFermiWitness w a) {s : ℂ} (hs : a < s.re) :
    AnalyticAt ℂ (witnessMellin w) s := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | a < z.re})
    (fun z hz => (hw.differentiableAt_witnessMellin hz).differentiableWithinAt)
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs

theorem IsFermiNymanWitness.correlation_order_of_bounded {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) {M : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) (ρ : rightStripZeros) :
    analyticOrderAt riemannZeta (ρ : ℂ) ≤ analyticOrderAt (fermiCorrelation w) (ρ : ℂ) := by
  have hρ0 : 0 < (ρ : ℂ).re := by linarith [ρ.2.2.1]
  have hρne0 : (ρ : ℂ) ≠ 0 := by intro h; simp [h] at hρ0
  have hρne1 : (ρ : ℂ) ≠ 1 := by
    intro h
    have := ρ.2.2.2
    simp [h] at this
  have hv : IsMellinFermiWitness (fun t => (starRingEnd ℂ) (w t)) 0 :=
    isMellinFermiWitness_of_bounded (Complex.continuous_conj.comp_continuousOn hw.1)
      (by simpa only [Complex.norm_conj] using hb) hw.2.2
  let A : ℂ → ℂ := fun s => fermiNymanSourceUnit 1 s *
    witnessMellin (fun t => (starRingEnd ℂ) (w t)) (1 - s)
  have harg : 0 < ((1 : ℂ) - (ρ : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [ρ.2.2.2]
  have hA : AnalyticAt ℂ A (ρ : ℂ) :=
    (analyticAt_fermiNymanSourceUnit one_pos hρne0).mul
      ((hv.analyticAt_witnessMellin harg).comp
        (analyticAt_const.sub analyticAt_id))
  have heq : fermiCorrelation w =ᶠ[𝓝 (ρ : ℂ)] A * riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ0,
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds ρ.2.2.2] with s hs0 hs1
    have hsne1 : s ≠ 1 := by intro h; simp [h] at hs1
    rw [fermiCorrelation, hv.correlationMellin_eq hs0 (by linarith),
      mellin_fermiNymanGen_of_mem one_pos ⟨hs0, hsne1⟩,
      fermiNymanMellinRHS_eq_unit_mul_zeta]
    change (fermiNymanSourceUnit 1 s * riemannZeta s) *
      witnessMellin (fun t => (starRingEnd ℂ) (w t)) (1 - s) = A s * riemannZeta s
    dsimp [A]
    ring
  rw [analyticOrderAt_congr heq,
    analyticOrderAt_mul hA (analyticOn_riemannZeta (ρ : ℂ) hρne1)]
  exact le_add_of_nonneg_left zero_le

theorem IsFermiNymanWitness.jetPacket_eq_zero_of_bounded {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) {M : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) : fermiMultiplicityJetPacket w = 0 := by
  funext a
  have hord : (rightStripMultiplicity a.1 : ℕ∞) ≤
      analyticOrderAt (fermiCorrelation w) (a.1 : ℂ) := by
    rw [rightStripMultiplicity_coe]
    exact hw.correlation_order_of_bounded hb a.1
  have hderiv := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hw.analyticAt_fermiCorrelation (by linarith [a.1.2.2.1]))).mp hord a.2 a.2.isLt
  change (starRingEnd ℂ) (iteratedDeriv a.2 (fermiCorrelation w) (a.1 : ℂ)) = 0
  rw [hderiv, map_zero]

theorem IsFermiNymanWitness.jetPacket_eq_zero_iff_bounded {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) :
    fermiMultiplicityJetPacket w = 0 ↔
      ∃ M : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M := by
  constructor
  · intro hJ
    exact bounded_of_continuous_dyadicSelfSimilar hw.1
      (fun t ht => hw.selfSimilar_of_jetPacket_eq_zero hJ ht)
  · rintro ⟨M, hM⟩
    exact hw.jetPacket_eq_zero_of_bounded hM

theorem IsFermiNymanWitness.jetPacket_eq_zero_iff_selfSimilar {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) :
    fermiMultiplicityJetPacket w = 0 ↔ ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t := by
  constructor
  · exact fun hJ t ht => hw.selfSimilar_of_jetPacket_eq_zero hJ ht
  · intro hs
    obtain ⟨M, hM⟩ := bounded_of_continuous_dyadicSelfSimilar hw.1 hs
    exact hw.jetPacket_eq_zero_of_bounded hM

/-- Actual witnesses with a uniform bound on the physical interval. -/
def boundedFermiWitnessSet : Set (ℝ → ℂ) :=
  {w | IsFermiNymanWitness w ∧ ∃ M : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M}

/-- Actual witnesses invisible to every right-strip submultiplicity correlation jet. -/
def fermiMultiplicityJetKernelSet : Set (ℝ → ℂ) :=
  {w | IsFermiNymanWitness w ∧ fermiMultiplicityJetPacket w = 0}

/-- The literal source identifies exactly the bounded part forgotten by the divisor coordinates. -/
theorem fermiMultiplicityJetKernelSet_eq_boundedFermiWitnessSet :
    fermiMultiplicityJetKernelSet = boundedFermiWitnessSet := by
  ext w
  constructor
  · rintro ⟨hw, hJ⟩
    exact ⟨hw, hw.jetPacket_eq_zero_iff_bounded.mp hJ⟩
  · rintro ⟨hw, hM⟩
    exact ⟨hw, hw.jetPacket_eq_zero_iff_bounded.mpr hM⟩

end RHTower
