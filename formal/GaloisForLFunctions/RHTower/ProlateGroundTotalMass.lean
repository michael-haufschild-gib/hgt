import GaloisForLFunctions.RHTower.ProlateWindowMass
import GaloisForLFunctions.RHTower.ProlateGroundGaussianLimit

/-!
# Total mass of the ground prolate profile

The window comparison pins the normalized rescaled profile `u_c(ξ) = Φ_c(ξ/√c)/Φ_c(0)` against the
Gaussian on every fixed window, and the aperture virial bounds the second moment.  Chebyshev turns
the second-moment bound into a tail bound that is uniform in the bandwidth, so the total mass

`N(c) = ∫_{−√c}^{√c} u_c²`

is squeezed between the window masses and converges to `∫_ℝ e^{−ξ²} = √π`.  Unwinding the
normalization, this is exactly the centre-mass asymptotic

`√(π/c)·Φ_c(0)² / ∫_{−1}^{1} Φ_c² → 1` .
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Uniform a priori bound for the phase vector of a normalized profile on the window. -/
def prolateWindowPhaseBound (K : ℝ) : ℝ :=
  Real.exp (max 1 (hermiteWindowBound K 0 + 2) * K)

theorem prolateWindowPhaseBound_pos (K : ℝ) : 0 < prolateWindowPhaseBound K := Real.exp_pos _

theorem prolateWindowEpsP_nonneg {c mu K : ℝ} {n : ℕ} (hc : 0 < c) :
    0 ≤ prolateWindowEpsP c mu K n := by
  rw [prolateWindowEpsP]
  have h1 : (0 : ℝ) ≤ 2 * |mu - (2 * (n : ℝ) + 1)| := by positivity
  have h2 : (0 : ℝ) ≤ 2 * (K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / c := by positivity
  linarith

theorem prolateWindowEpsQ_nonneg {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    0 ≤ prolateWindowEpsQ c K := by
  rw [prolateWindowEpsQ]
  positivity

theorem hermiteWindowBound_nonneg (K : ℝ) (n : ℕ) : 0 ≤ hermiteWindowBound K n := by
  rw [hermiteWindowBound]
  positivity

/-- **Uniform a priori phase bound.**  Once both coefficient defects are at most one, a normalized
solution of the rescaled prolate equation is bounded on the window by a constant depending only on
the window. -/
theorem normalizedProlate_phase_le {c mu K : ℝ} {u u' u'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hequ : ∀ x ∈ Icc (0 : ℝ) K,
      u'' x = rescaledProlateP c mu x * u x + rescaledProlateQ c x * u' x)
    (h0 : u 0 = 1) (h0' : u' 0 = 0)
    (hP : prolateWindowEpsP c mu K 0 ≤ 1) (hQ : prolateWindowEpsQ c K ≤ 1) :
    ∀ x ∈ Icc (0 : ℝ) K, max |u x| |u' x| ≤ prolateWindowPhaseBound K := by
  have hc : 0 < c := pos_of_window hK hcK
  have hbase := prolateProfile_window_phase_le (n := 0) hK hcK hu hu' hequ
  intro x hx
  refine le_trans (hbase x hx) ?_
  have hval : max |u 0| |u' 0| = 1 := by
    rw [h0, h0']
    simp
  rw [hval, one_mul, prolateWindowPhaseBound]
  refine Real.exp_le_exp.2 ?_
  have hrate : max 1 ((hermiteWindowBound K 0 + prolateWindowEpsP c mu K 0)
      + prolateWindowEpsQ c K) ≤ max 1 (hermiteWindowBound K 0 + 2) := by
    refine max_le_max le_rfl ?_
    linarith
  have hratepos : (0 : ℝ) ≤ max 1 ((hermiteWindowBound K 0 + prolateWindowEpsP c mu K 0)
      + prolateWindowEpsQ c K) := le_trans zero_le_one (le_max_left _ _)
  have hxK : x - 0 ≤ K := by
    have := hx.2
    linarith
  have hx0 : (0 : ℝ) ≤ x - 0 := by
    have := hx.1
    linarith
  exact mul_le_mul hrate hxK hx0 (le_trans hratepos hrate)

/-- Envelope for the window mass defect: the Grönwall envelope, times the squaring factor and the
window length. -/
def prolateWindowMassEnvelope (c mu K : ℝ) : ℝ :=
  (((prolateWindowEpsP c mu K 0 + prolateWindowEpsQ c K) * prolateWindowPhaseBound K
      / max 1 (hermiteWindowBound K 0))
    * (Real.exp (max 1 (hermiteWindowBound K 0) * (K - 0)) - 1))
    * (prolateWindowPhaseBound K + 1) * (2 * K)

theorem tendsto_prolateWindowMassEnvelope {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K : ℝ}
    (hmu : Tendsto mu L (𝓝 1)) (hc : Tendsto c L atTop) :
    Tendsto (fun i => prolateWindowMassEnvelope (c i) (mu i) K) L (𝓝 0) := by
  have hbase : Tendsto (fun i => ((prolateWindowEpsP (c i) (mu i) K 0 + prolateWindowEpsQ (c i) K)
      * prolateWindowPhaseBound K / max 1 (hermiteWindowBound K 0))
        * (Real.exp (max 1 (hermiteWindowBound K 0) * (K - 0)) - 1)) L (𝓝 0) := by
    refine tendsto_prolateWindow_envelope (n := 0) (B := prolateWindowPhaseBound K) ?_ hc
    simpa using hmu
  have h1 := hbase.mul_const (prolateWindowPhaseBound K + 1)
  have h2 := h1.mul_const (2 * K)
  simpa [prolateWindowMassEnvelope] using h2

/-- **Window mass of a normalized prolate profile.**  The window mass differs from the Gaussian
window mass by at most the envelope. -/
theorem prolateGround_windowMass_bound
    {c mu chi lam K : ℝ} {Phi : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0) (heven : Function.Even Phi) (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hmuval : mu = c * radialSeparationRatio c chi)
    (hP : prolateWindowEpsP c mu K 0 ≤ 1) (hQ : prolateWindowEpsQ c K ≤ 1) :
    |(∫ x in (-K)..K, (normalizedProlateProfile c Phi x) ^ (2 : ℕ))
        - ∫ x in (-K)..K, Real.exp (-(x ^ (2 : ℕ)))|
      ≤ prolateWindowMassEnvelope c mu K := by
  obtain ⟨hu, hu', hequ0, hval0, hval0'⟩ :=
    normalizedProlate_window_package (K := K) hK hcK hsm hne heven hlam hband heig
  have hequ : ∀ x ∈ Icc (0 : ℝ) K,
      normalizedProlateDeriv2 c Phi x
        = rescaledProlateP c mu x * normalizedProlateProfile c Phi x
          + rescaledProlateQ c x * normalizedProlateDeriv c Phi x := by
    rw [hmuval]
    exact hequ0
  have hB : ∀ x ∈ Icc (0 : ℝ) K,
      max |normalizedProlateProfile c Phi x| |normalizedProlateDeriv c Phi x|
        ≤ prolateWindowPhaseBound K :=
    normalizedProlate_phase_le hK hcK hu hu' hequ hval0 hval0' hP hQ
  have hgron := prolateProfile_window_gaussian_dist_le (c := c) (mu := mu) (K := K)
    (B := prolateWindowPhaseBound K) hK hcK hu hu' hequ hB hval0 hval0'
  -- window estimate for the profile itself, then for its square
  have hdist0 : ∀ x ∈ Icc (0 : ℝ) K,
      |normalizedProlateProfile c Phi x - gaussianProfile x|
        ≤ ((prolateWindowEpsP c mu K 0 + prolateWindowEpsQ c K) * prolateWindowPhaseBound K
            / max 1 (hermiteWindowBound K 0))
          * (Real.exp (max 1 (hermiteWindowBound K 0) * (K - 0)) - 1) := by
    intro x hx
    exact le_trans (le_max_left _ _) (hgron x hx)
  have heu : Function.Even (normalizedProlateProfile c Phi) :=
    even_normalizedProlateProfile heven
  have hdist := abs_sub_le_of_even_window heu hdist0
  have hBfull : ∀ x ∈ Icc (-K) K, |normalizedProlateProfile c Phi x| ≤ prolateWindowPhaseBound K :=
    abs_le_of_even_window heu (fun x hx => le_trans (le_max_left _ _) (hB x hx))
  have hsq := abs_sq_sub_le_of_window hdist hBfull
  have hcont : Continuous (normalizedProlateProfile c Phi) :=
    continuous_normalizedProlateProfile hsm
  have hfin := abs_windowMass_sub_le (K := K) hK.le hcont hsq
  simpa [prolateWindowMassEnvelope, mul_assoc] using hfin

/-- The normalized second moment inherits the separation bound. -/
theorem normalizedProlate_secondMoment_le
    {c chi : ℝ} {Phi : ℝ → ℝ} (hc : 0 < c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), xi ^ (2 : ℕ) * (normalizedProlateProfile c Phi xi) ^ (2 : ℕ))
      ≤ (c * radialSeparationRatio c chi)
        * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi xi) ^ (2 : ℕ) := by
  have hkey := integral_rescaled_secondMoment_le hc hsm heig
  have e1 : ∀ xi : ℝ, xi ^ (2 : ℕ) * (normalizedProlateProfile c Phi xi) ^ (2 : ℕ)
      = (1 / (Phi 0) ^ (2 : ℕ)) * (xi ^ (2 : ℕ) * (prolateHermiteRescale c Phi xi) ^ (2 : ℕ)) := by
    intro xi
    rw [normalizedProlateProfile, div_pow]
    ring
  have e2 : ∀ xi : ℝ, (normalizedProlateProfile c Phi xi) ^ (2 : ℕ)
      = (1 / (Phi 0) ^ (2 : ℕ)) * (prolateHermiteRescale c Phi xi) ^ (2 : ℕ) := by
    intro xi
    rw [normalizedProlateProfile, div_pow]
    ring
  simp_rw [e1, e2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hnn : (0 : ℝ) ≤ 1 / (Phi 0) ^ (2 : ℕ) := by positivity
  nlinarith [hkey, hnn]

/-- **Chebyshev bound on the normalized total mass.**  Outside the window at most the fraction
`2/K²` of the total mass survives. -/
theorem normalizedProlate_chebyshev
    {c mu chi K : ℝ} {Phi : ℝ → ℝ} (hc : 0 < c) (hK : 0 < K) (hKc : K ≤ Real.sqrt c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x)
    (hmuval : mu = c * radialSeparationRatio c chi) (hmu2 : mu ≤ 2) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi xi) ^ (2 : ℕ))
        * (1 - 2 / K ^ (2 : ℕ))
      ≤ ∫ xi in (-K)..K, (normalizedProlateProfile c Phi xi) ^ (2 : ℕ) := by
  have hcont : Continuous (normalizedProlateProfile c Phi) :=
    continuous_normalizedProlateProfile hsm
  have htail := window_tail_le_of_secondMoment (f := normalizedProlateProfile c Phi)
    (K := K) (R := Real.sqrt c) hK hKc hcont
  have hmom := normalizedProlate_secondMoment_le hc hsm heig
  have hNnn : (0 : ℝ) ≤ ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
      (normalizedProlateProfile c Phi xi) ^ (2 : ℕ) := by
    refine intervalIntegral.integral_nonneg ?_ (fun x _ => sq_nonneg _)
    have : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg c
    linarith
  have hKsq : (0 : ℝ) < 1 / K ^ (2 : ℕ) := by positivity
  rw [hmuval] at hmu2
  have hchain : (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
      xi ^ (2 : ℕ) * (normalizedProlateProfile c Phi xi) ^ (2 : ℕ))
      ≤ 2 * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi xi) ^ (2 : ℕ) := by
    refine le_trans hmom ?_
    exact mul_le_mul_of_nonneg_right hmu2 hNnn
  have hdiv : (2 : ℝ) / K ^ (2 : ℕ) = (1 / K ^ (2 : ℕ)) * 2 := by ring
  rw [hdiv]
  nlinarith [htail, hchain, hKsq]

/-- The centre-mass ratio whose limit the card records. -/
def prolateCentreMassRatio (c : ℝ) (Phi : ℝ → ℝ) : ℝ :=
  Real.sqrt (Real.pi / c) * (Phi 0) ^ (2 : ℕ) / ∫ x in (-1 : ℝ)..1, (Phi x) ^ (2 : ℕ)

/-- The centre-mass ratio is exactly `√π` divided by the normalized total mass. -/
theorem prolateCentreMassRatio_mul_totalMass
    {c : ℝ} {Phi : ℝ → ℝ} (hc : 0 < c) (h0 : Phi 0 ≠ 0)
    (hS : (∫ x in (-1 : ℝ)..1, (Phi x) ^ (2 : ℕ)) ≠ 0) :
    prolateCentreMassRatio c Phi
        * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi xi) ^ (2 : ℕ)
      = Real.sqrt Real.pi := by
  have e2 : ∀ xi : ℝ, (normalizedProlateProfile c Phi xi) ^ (2 : ℕ)
      = (1 / (Phi 0) ^ (2 : ℕ)) * (prolateHermiteRescale c Phi xi) ^ (2 : ℕ) := by
    intro xi
    rw [normalizedProlateProfile, div_pow]
    ring
  simp_rw [e2]
  rw [intervalIntegral.integral_const_mul, integral_rescaled_sq hc]
  have hsc : Real.sqrt (Real.pi / c) * Real.sqrt c = Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (div_nonneg Real.pi_nonneg hc.le) c, div_mul_cancel₀ _ hc.ne']
  rw [prolateCentreMassRatio]
  field_simp
  nlinarith [hsc, sq_nonneg (Phi 0)]

/-- **Uniform total mass of a normalized prolate profile.**  The a priori phase bound on one window
plus the second-moment estimate caps the whole rescaled mass, with a constant depending only on the
window and the separation bound. -/
theorem normalizedProlate_total_mass_le {c mu chi lam K : ℝ} {Phi : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0) (heven : Function.Even Phi) (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hmuval : mu = c * radialSeparationRatio c chi)
    (hP : prolateWindowEpsP c mu K 0 ≤ 1) (hQ : prolateWindowEpsQ c K ≤ 1) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi xi) ^ (2 : ℕ))
        * (1 - mu / K ^ (2 : ℕ))
      ≤ 2 * K * prolateWindowPhaseBound K ^ (2 : ℕ) := by
  have hc : 0 < c := pos_of_window hK hcK
  obtain ⟨hu, hu', hequ0, hval0, hval0'⟩ :=
    normalizedProlate_window_package (K := K) hK hcK hsm hne heven hlam hband heig
  have hequ : ∀ x ∈ Icc (0 : ℝ) K,
      normalizedProlateDeriv2 c Phi x
        = rescaledProlateP c mu x * normalizedProlateProfile c Phi x
          + rescaledProlateQ c x * normalizedProlateDeriv c Phi x := by
    rw [hmuval]
    exact hequ0
  have hB0 := normalizedProlate_phase_le hK hcK hu hu' hequ hval0 hval0' hP hQ
  have heu : Function.Even (normalizedProlateProfile c Phi) :=
    even_normalizedProlateProfile heven
  have hBfull : ∀ x ∈ Icc (-K) K,
      |normalizedProlateProfile c Phi x| ≤ prolateWindowPhaseBound K :=
    abs_le_of_even_window heu (fun x hx => le_trans (le_max_left _ _) (hB0 x hx))
  have hKS : K ≤ Real.sqrt c := by
    calc K = Real.sqrt (K ^ (2 : ℕ)) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg K])
  have hmom : (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
      xi ^ (2 : ℕ) * (normalizedProlateProfile c Phi xi) ^ (2 : ℕ))
      ≤ mu * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi xi) ^ (2 : ℕ) := by
    rw [hmuval]
    exact normalizedProlate_secondMoment_le hc hsm (fun x _ => heig x)
  exact total_mass_le_of_window_bound hK hKS (continuous_normalizedProlateProfile hsm)
    hBfull hmom

/-- **The centre-mass asymptotic.**  For the variationally selected ground family the centre value,
the bandwidth and the aperture mass satisfy

`√(π/c)·Φ_c(0)² / ∫_{−1}^{1} Φ_c² → 1` .

The window comparison against the Gaussian pins the profile on every fixed window; the aperture
virial pins the second moment, hence by Chebyshev the tail; the two together squeeze the total
mass of the normalized profile onto `∫_ℝ e^{−ξ²} = √π`. -/
theorem tendsto_prolateGround_centreMass :
    ∃ Psi : ℝ → ℝ → ℝ,
      (∀ c : ℝ, 0 < c → ∃ lam chi : ℝ, lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Psi c) ∧ Psi c ≠ 0 ∧ Function.Even (Psi c) ∧
        (∀ x : ℝ, bandTransform c (Psi c) x = lam * Psi c x) ∧
        (∀ x : ℝ, prolateSLAction c (Psi c) x = chi * Psi c x)) ∧
      Tendsto (fun c => prolateCentreMassRatio c (Psi c)) atTop (𝓝 1) := by
  obtain ⟨mu, Psi, hmu, hfam⟩ := exists_ground_family
  refine ⟨Psi, ?_, ?_⟩
  · intro c hc
    obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, _⟩ := hfam c hc
    exact ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate⟩
  -- the two coefficient defects vanish, so eventually both are at most one
  have hepsP : ∀ K : ℝ, ∀ᶠ c in atTop, prolateWindowEpsP c (mu c) K 0 ≤ 1 := by
    intro K
    have h := tendsto_prolateWindowEpsP (n := 0) (K := K) (c := fun x : ℝ => x)
      (by simpa using hmu) tendsto_id
    filter_upwards [h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with c hc
    exact hc.le
  have hepsQ : ∀ K : ℝ, ∀ᶠ c in atTop, prolateWindowEpsQ c K ≤ 1 := by
    intro K
    have h := tendsto_prolateWindowEpsQ (K := K) (c := fun x : ℝ => x) tendsto_id
    filter_upwards [h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with c hc
    exact hc.le
  have hmu2 : ∀ᶠ c in atTop, mu c ≤ 2 := by
    filter_upwards [hmu.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))] with c hc
    exact hc.le
  have hsqrt : ∀ K : ℝ, 0 < K → ∀ᶠ c in atTop, K ≤ Real.sqrt c := by
    intro K hK
    filter_upwards [eventually_ge_atTop (K ^ (2 : ℕ))] with c hc
    calc K = Real.sqrt (K ^ (2 : ℕ)) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc
  -- the normalized total mass converges to the Gaussian mass
  have htotal : Tendsto
      (fun c => ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        (normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ)) atTop (𝓝 (Real.sqrt Real.pi)) := by
    refine tendsto_total_of_window (M := 2)
      (W := fun K c => ∫ x in (-K)..K, (normalizedProlateProfile c (Psi c) x) ^ (2 : ℕ))
      (G := fun K => ∫ x in (-K)..K, Real.exp (-(x ^ (2 : ℕ)))) (by norm_num) ?_ ?_ ?_
      tendsto_gaussianWindow
    · intro K hK _
      filter_upwards [eventually_gt_atTop (0 : ℝ), hsqrt K hK] with c hc hKc
      obtain ⟨lam, chi, hlam, hsm, _⟩ := hfam c hc
      exact window_le_total hKc (continuous_normalizedProlateProfile hsm)
    · intro K hK _
      filter_upwards [eventually_gt_atTop (0 : ℝ), hsqrt K hK, hmu2] with c hc hKc hm
      obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
      exact normalizedProlate_chebyshev hc hK hKc hsm (fun x _ => hprolate x) hval hm
    · intro K hK _
      have henv := tendsto_prolateWindowMassEnvelope (mu := mu) (c := fun x : ℝ => x) (K := K)
        hmu tendsto_id
      have hbnd : ∀ᶠ c in atTop,
          ‖(∫ x in (-K)..K, (normalizedProlateProfile c (Psi c) x) ^ (2 : ℕ))
            - ∫ x in (-K)..K, Real.exp (-(x ^ (2 : ℕ)))‖ ≤ prolateWindowMassEnvelope c (mu c) K := by
        filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2 * K ^ (2 : ℕ)),
          hepsP K, hepsQ K] with c hc hcK hP hQ
        obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
        exact prolateGround_windowMass_bound hK hcK hsm hne heven hlam hband hprolate hval hP hQ
      have hzero := squeeze_zero_norm' hbnd henv
      have hadd := hzero.add_const (∫ x in (-K)..K, Real.exp (-(x ^ (2 : ℕ))))
      simpa using hadd
  -- unwind the normalization
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlim : Tendsto (fun c => Real.sqrt Real.pi
      / ∫ xi in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ))
      atTop (𝓝 1) := by
    have := (tendsto_const_nhds (α := ℝ) (f := atTop (α := ℝ))
      (x := Real.sqrt Real.pi)).div htotal hpi.ne'
    simpa [div_self hpi.ne', Pi.div_def] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htotal.eventually (eventually_gt_nhds hpi)] with c hc hN
  obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, hposS, _⟩ := hfam c hc
  have h0 : Psi c 0 ≠ 0 :=
    value_zero_ne_of_even_joint_prolate_band_eigen hsm hne heven hlam hband hprolate
  have hkey := prolateCentreMassRatio_mul_totalMass hc h0 hposS.ne'
  field_simp at hkey ⊢
  linarith [hkey]

end RHTower
