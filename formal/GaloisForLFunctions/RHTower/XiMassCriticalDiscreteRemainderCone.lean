import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderSymmetry

/-!
# Superluminal-tail removal for the discrete critical Xi mass current

For nonnegative vertical height `u`, shift the mass Fourier contour by any depth
`1/2 < d < a`.  The true outgoing derivative then decays as `exp (d*u - d*h)`.  Combined only
with the elementary bound `|psi(N)-N| <= 8*N`, this makes the current beyond

`h = d*u / (d - 1/2)`

uniformly integrable in `u`.  Consequently the one-sided exact RH criterion is equivalent to
uniform boundedness of a finite, linearly expanding mass light-cone current.  The infinite tail is
not an arithmetic obligation.

All estimates below are estimates of the actual integrals.  No numerical computation, asymptotic
replacement, PNT remainder, or cancellation hypothesis is used.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Height-independent moment factor in the depth-`d` outgoing derivative bound. -/
noncomputable def xiMassCriticalOutgoingDeepShiftBound (sigma d : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
    ∫ x : ℝ, (|x| + d) * Real.exp (-(sigma * |x|))

theorem xiMassCriticalOutgoingDeepShiftBound_nonneg {sigma d : ℝ} (hd : 0 ≤ d) :
    0 ≤ xiMassCriticalOutgoingDeepShiftBound sigma d := by
  unfold xiMassCriticalOutgoingDeepShiftBound
  exact add_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg fun _ => Real.exp_nonneg _))
    (integral_nonneg fun x =>
      mul_nonneg (add_nonneg (abs_nonneg x) hd) (Real.exp_nonneg _))

/-- The critically normalized raw discrete remainder coefficient has the elementary
`8*exp(h/2)` envelope. -/
theorem norm_xiMassCriticalDiscreteRemainderCoefficient_le (h : ℝ) :
    ‖(((Real.exp (-h / 2) * psiRemainder ⌊Real.exp h⌋₊ : ℝ) : ℂ))‖ ≤
      8 * Real.exp (h / 2) := by
  have hR := abs_psiRemainder_le ⌊Real.exp h⌋₊
  have hfloor : (⌊Real.exp h⌋₊ : ℝ) ≤ Real.exp h :=
    Nat.floor_le (Real.exp_pos h).le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-h / 2) * |psiRemainder ⌊Real.exp h⌋₊| ≤
        Real.exp (-h / 2) * (8 * (⌊Real.exp h⌋₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left hR (Real.exp_nonneg _)
    _ ≤ Real.exp (-h / 2) * (8 * Real.exp h) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfloor (by norm_num)) (Real.exp_nonneg _)
    _ = 8 * Real.exp (h / 2) := by
      rw [show Real.exp (-h / 2) * (8 * Real.exp h) =
        8 * (Real.exp (-h / 2) * Real.exp h) by ring_nf]
      rw [← Real.exp_add]
      congr 1
      ring_nf

/-- Actual integral-kernel density bound in the outgoing region. -/
theorem norm_xiMassCriticalDiscreteRemainderDensity_le_deepShift
    {a sigma d u h : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ ≤
      8 * xiMassCriticalOutgoingDeepShiftBound sigma d *
        Real.exp (d * u + (1 / 2 - d) * h) := by
  have hD := norm_xiMassCriticalOutgoingDerivative_deepShift_le
    (a := a) (sigma := sigma) (d := d) (by linarith) hda hsigma u h
  rw [abs_of_nonneg hu] at hD
  rw [xiMassCriticalDiscreteRemainderDensity, norm_mul]
  calc
    ‖(((Real.exp (-h / 2) * psiRemainder ⌊Real.exp h⌋₊ : ℝ) : ℂ))‖ *
        ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
      (8 * Real.exp (h / 2)) *
        ‖xiMassCriticalOutgoingDerivative a sigma u h‖ :=
      mul_le_mul_of_nonneg_right
        (norm_xiMassCriticalDiscreteRemainderCoefficient_le h) (norm_nonneg _)
    _ ≤ (8 * Real.exp (h / 2)) *
        (Real.exp (u * d - h * d) *
          xiMassCriticalOutgoingDeepShiftBound sigma d) :=
      mul_le_mul_of_nonneg_left
        (by simpa [xiMassCriticalOutgoingDeepShiftBound] using hD) (by positivity)
    _ = 8 * xiMassCriticalOutgoingDeepShiftBound sigma d *
        Real.exp (d * u + (1 / 2 - d) * h) := by
      rw [show (8 * Real.exp (h / 2)) *
          (Real.exp (u * d - h * d) *
            xiMassCriticalOutgoingDeepShiftBound sigma d) =
        8 * xiMassCriticalOutgoingDeepShiftBound sigma d *
          (Real.exp (h / 2) * Real.exp (u * d - h * d)) by ring_nf]
      rw [← Real.exp_add]
      ring_nf

/-- Discrete critical current after a logarithmic-time cutoff. -/
noncomputable def xiMassCriticalDiscreteRemainderTailFlux
    (a sigma u H : ℝ) : ℂ :=
  ∫ h in Ioi H, xiMassCriticalDiscreteRemainderDensity a sigma u h

/-- Exact exponential tail integral bound at arbitrary nonnegative cutoff. -/
theorem norm_xiMassCriticalDiscreteRemainderTailFlux_le
    {a sigma d u H : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    (hu : 0 ≤ u) (hH : 0 ≤ H) :
    ‖xiMassCriticalDiscreteRemainderTailFlux a sigma u H‖ ≤
      (8 * xiMassCriticalOutgoingDeepShiftBound sigma d * Real.exp (d * u)) *
        (-Real.exp ((1 / 2 - d) * H) / (1 / 2 - d)) := by
  let J : ℝ := xiMassCriticalOutgoingDeepShiftBound sigma d
  let b : ℝ := 1 / 2 - d
  have hb : b < 0 := by dsimp [b]; linarith
  have hJ : 0 ≤ J := xiMassCriticalOutgoingDeepShiftBound_nonneg (by linarith)
  have hleft : IntegrableOn
      (xiMassCriticalDiscreteRemainderDensity a sigma u) (Ioi H) := by
    have hfull := integrableOn_xiMassCriticalDiscreteRemainderDensity
      (a := a) (sigma := sigma) (lt_trans hdhalf hda) hsigma u
    exact hfull.mono_set (Ioi_subset_Ioi hH)
  have hright : IntegrableOn
      (fun h : ℝ => (8 * J * Real.exp (d * u)) * Real.exp (b * h)) (Ioi H) :=
    (integrableOn_exp_mul_Ioi hb H).const_mul _
  have hmono :
      (∫ h in Ioi H, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) ≤
        ∫ h in Ioi H, (8 * J * Real.exp (d * u)) * Real.exp (b * h) := by
    apply integral_mono_ae hleft.norm hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hdensity := norm_xiMassCriticalDiscreteRemainderDensity_le_deepShift
      hdhalf hda hsigma hu (h := h)
    calc
      ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ ≤
          8 * J * Real.exp (d * u + b * h) := by
        simpa only [J, b] using hdensity
      _ = (8 * J * Real.exp (d * u)) * Real.exp (b * h) := by
        rw [Real.exp_add]
        ring_nf
  calc
    ‖xiMassCriticalDiscreteRemainderTailFlux a sigma u H‖ ≤
        ∫ h in Ioi H, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi H, (8 * J * Real.exp (d * u)) * Real.exp (b * h) := hmono
    _ = (8 * J * Real.exp (d * u)) * (-Real.exp (b * H) / b) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hb H]
    _ = _ := by simp only [J, b]

/-- Beyond slope `d/(d-1/2)`, the complete infinite remainder tail is uniformly bounded in
nonnegative vertical height. -/
theorem norm_xiMassCriticalDiscreteRemainder_superluminalTailFlux_le
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    ‖xiMassCriticalDiscreteRemainderTailFlux
        a sigma u (d * u / (d - 1 / 2))‖ ≤
      8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) := by
  have hden : 0 < d - 1 / 2 := by linarith
  have hH : 0 ≤ d * u / (d - 1 / 2) := by positivity
  have hb : 1 / 2 - d = -(d - 1 / 2) := by ring_nf
  have h := norm_xiMassCriticalDiscreteRemainderTailFlux_le
    hdhalf hda hsigma hu hH
  calc
    ‖xiMassCriticalDiscreteRemainderTailFlux
        a sigma u (d * u / (d - 1 / 2))‖ ≤
        (8 * xiMassCriticalOutgoingDeepShiftBound sigma d * Real.exp (d * u)) *
          (-Real.exp ((1 / 2 - d) * (d * u / (d - 1 / 2))) /
            (1 / 2 - d)) := h
    _ = 8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) := by
      have hdenne : d - 1 / 2 ≠ 0 := by linarith
      have hexp : d * u + (1 / 2 - d) * (d * u / (d - 1 / 2)) = 0 := by
        rw [hb]
        calc
          d * u + -(d - 1 / 2) * (d * u / (d - 1 / 2)) =
              d * u - (d * u / (d - 1 / 2)) * (d - 1 / 2) := by ring_nf
          _ = d * u - d * u := by rw [div_mul_cancel₀ _ hdenne]
          _ = 0 := sub_self _
      have hexpprod : Real.exp (d * u) *
          Real.exp ((1 / 2 - d) * (d * u / (d - 1 / 2))) = 1 := by
        rw [← Real.exp_add, hexp, Real.exp_zero]
      rw [show (8 * xiMassCriticalOutgoingDeepShiftBound sigma d * Real.exp (d * u)) *
          (-Real.exp ((1 / 2 - d) * (d * u / (d - 1 / 2))) / (1 / 2 - d)) =
        8 * xiMassCriticalOutgoingDeepShiftBound sigma d *
          (-(Real.exp (d * u) *
            Real.exp ((1 / 2 - d) * (d * u / (d - 1 / 2)))) /
              (1 / 2 - d)) by ring_nf,
        hexpprod, hb]
      field_simp [hdenne]

/-- Finite current inside the mass-dependent logarithmic light cone. -/
noncomputable def xiMassCriticalDiscreteRemainderConeFlux
    (a sigma d u : ℝ) : ℂ :=
  ∫ h in Ioc (0 : ℝ) (d * u / (d - 1 / 2)),
    xiMassCriticalDiscreteRemainderDensity a sigma u h

/-- Exact split into the finite cone and the uniformly bounded superluminal tail. -/
theorem xiMassCriticalDiscreteRemainderFlux_eq_cone_add_tail
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    xiMassCriticalDiscreteRemainderFlux a sigma u =
      xiMassCriticalDiscreteRemainderConeFlux a sigma d u +
        xiMassCriticalDiscreteRemainderTailFlux
          a sigma u (d * u / (d - 1 / 2)) := by
  let H : ℝ := d * u / (d - 1 / 2)
  have hH : 0 ≤ H := by
    dsimp [H]
    have : 0 < d - 1 / 2 := by linarith
    positivity
  have hfull := integrableOn_xiMassCriticalDiscreteRemainderDensity
    (a := a) (sigma := sigma) (lt_trans hdhalf hda) hsigma u
  have hhead : IntegrableOn
      (xiMassCriticalDiscreteRemainderDensity a sigma u) (Ioc 0 H) :=
    hfull.mono_set (fun _ hh => hh.1)
  have htail : IntegrableOn
      (xiMassCriticalDiscreteRemainderDensity a sigma u) (Ioi H) :=
    hfull.mono_set (Ioi_subset_Ioi hH)
  have hdisj : Disjoint (Ioc (0 : ℝ) H) (Ioi H) := by
    rw [Set.disjoint_left]
    intro h hh ht
    exact (not_lt_of_ge hh.2) ht
  have hcover : Ioc (0 : ℝ) H ∪ Ioi H = Ioi 0 := Ioc_union_Ioi_eq_Ioi hH
  rw [xiMassCriticalDiscreteRemainderFlux,
    xiMassCriticalDiscreteRemainderConeFlux,
    xiMassCriticalDiscreteRemainderTailFlux]
  change (∫ h in Ioi (0 : ℝ), xiMassCriticalDiscreteRemainderDensity a sigma u h) =
    (∫ h in Ioc (0 : ℝ) H, xiMassCriticalDiscreteRemainderDensity a sigma u h) +
      ∫ h in Ioi H, xiMassCriticalDiscreteRemainderDensity a sigma u h
  rw [← hcover]
  exact setIntegral_union hdisj measurableSet_Ioi hhead htail

/-- Uniform bound on the finite current inside one nonnegative mass light cone. -/
def XiMassCriticalDiscreteRemainderConeFluxLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalDiscreteRemainderConeFlux a sigma d u‖ ≤ C

/-- Removing or restoring the superluminal tail preserves the one-sided line-bound problem. -/
theorem xiMassCriticalDiscreteRemainderFluxNonnegativeLineBound_iff_cone
    {a sigma d : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    XiMassCriticalDiscreteRemainderFluxNonnegativeLineBound a sigma ↔
      XiMassCriticalDiscreteRemainderConeFluxLineBound a sigma d := by
  let B : ℝ :=
    8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2)
  have htail : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalDiscreteRemainderTailFlux
        a sigma u (d * u / (d - 1 / 2))‖ ≤ B :=
    fun u hu => norm_xiMassCriticalDiscreteRemainder_superluminalTailFlux_le
      hdhalf hda hsigma hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsplit := xiMassCriticalDiscreteRemainderFlux_eq_cone_add_tail
      hdhalf hda hsigma hu
    have hcone : xiMassCriticalDiscreteRemainderConeFlux a sigma d u =
        xiMassCriticalDiscreteRemainderFlux a sigma u -
          xiMassCriticalDiscreteRemainderTailFlux
            a sigma u (d * u / (d - 1 / 2)) := by
      rw [hsplit]
      ring_nf
    rw [hcone]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (htail u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    rw [xiMassCriticalDiscreteRemainderFlux_eq_cone_add_tail hdhalf hda hsigma hu]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (htail u hu))

/-- **Finite-cone exact open core.**  RH is equivalent to uniform control of the discrete
Selberg-remainder current only inside any legal expanding mass cone. -/
theorem riemannHypothesis_iff_xiMassCriticalDiscreteRemainderConeFluxLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔
      XiMassCriticalDiscreteRemainderConeFluxLineBound a sigma d := by
  exact (riemannHypothesis_iff_xiMassCriticalDiscreteRemainderFluxNonnegativeLineBound
    hhalf hca hsigma).trans
      (xiMassCriticalDiscreteRemainderFluxNonnegativeLineBound_iff_cone
        hdhalf hda hsigma)

end


end RHTower
