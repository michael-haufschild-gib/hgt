import GaloisForLFunctions.HTGeometry.ConjugatedTransportRepresentation
import GaloisForLFunctions.HTGeometry.HalfLineIntegratingFactor
import GaloisForLFunctions.HTGeometry.IntervalTestSeparation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaHalfLineClassification

/-!
# The distributional half-line classification of the Gamma frequency equation

A tempered `X`-valued distribution satisfying the Gamma frequency equation

`u(φ) + 2 u(η φ') + i u(η r φ) - i T(u(η φ)) = 0`

on a compact subinterval of the positive frequency half-line is, on that subinterval, the locally
integrable function `η^{-1/2} Q(η) c` for a single channel vector `c`, where `Q` is the Gamma
transport.  The proof divides the equation by the coordinate, conjugates by the cut-off integrating
factor `η^{1/2} exp(-(i/2)∫ r)`, and applies the constant-coefficient representation theorem for
distributional transport equations.
-/

open Set SchwartzMap Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The homogeneous Gamma profile away from the origin, `|η|^{-1/2}Q(η)c`. -/
def gammaFrequencyProfile (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (c : X) (t : ℝ) : X :=
  (|t| ^ (-(1 : ℝ) / 2)) • gammaTransport Rint T t c

/-- **The distributional half-line classification.**  A tempered distributional solution of the
Gamma frequency equation on a compact subinterval of the positive half-line is the Gamma transport
applied to a single channel vector. -/
theorem exists_channel_vector_distributional (T : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    {Rint r : ℝ → ℝ} {a b : ℝ} (hab : a < b) (h0 : (0 : ℝ) ∉ Icc a b)
    (hRint : ContDiff ℝ (⊤ : ℕ∞) Rint) (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hq : Function.HasTemperateGrowth (fun x : ℝ => ((x * r x : ℝ) : ℂ)))
    (hEq : ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ))
        + I • u (mulTemperateCLM hq φ) - I • T (u (coordMulCLM φ)) = 0) :
    ∃ c : X, ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c t := by
  -- the frequency remainder is smooth
  have hderivEq : deriv Rint = r := funext fun x => (hRderiv x).deriv
  have hr : ContDiff ℝ (⊤ : ℕ∞) r := by
    have := (contDiff_infty_iff_deriv.mp hRint).2
    rwa [hderivEq] at this
  -- the cutoff and the multipliers it produces
  obtain ⟨χ, δ, hδpos, hχsm, hχcs, hχone, hχzero⟩ := exists_interval_cutoff hab h0
  have hε : (0 : ℝ) < 2 * δ := by linarith
  have hIccU : Icc a b ⊆ Ioo (a - δ) (b + δ) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hUnhds : ∀ x ∈ Icc a b, ∀ᶠ y in nhds x, χ y = 1 := by
    intro x hx
    filter_upwards [(isOpen_Ioo (a := a - δ) (b := b + δ)).mem_nhds (hIccU hx)] with y hy
    exact hχone y hy
  have hIccne : ∀ x ∈ Icc a b, x ≠ 0 := by
    intro x hx hcon
    exact h0 (hcon ▸ hx)
  have hIccone : ∀ x ∈ Icc a b, χ x = 1 := fun x hx => hχone x (hIccU hx)
  set A : X →L[ℂ] X := ((-I / 2 : ℂ)) • T with hA
  have hinv := hasTemperateGrowth_invCut hχsm hχcs hε hχzero
  have hm := hasTemperateGrowth_gammaMultiplier hχsm hχcs hε hχzero hr
  have hgfac := hasTemperateGrowth_sqrtFactor hχsm hχcs hε hχzero hRint
  have hginv := hasTemperateGrowth_sqrtFactorInv hχsm hχcs hε hχzero hRint
  have hrcut := hasTemperateGrowth_rCut hχsm hχcs hr
  -- dividing by the coordinate is inverse to multiplying by it, on the interval
  have hdiv : ∀ θ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Icc a b → (θ : ℝ → ℂ) x = 0) →
      coordMulCLM (mulTemperateCLM hinv θ) = θ := by
    intro θ hθ
    refine SchwartzMap.ext fun x => ?_
    rw [coordMulCLM_apply, mulTemperateCLM_apply]
    by_cases hx : x ∈ Icc a b
    · have hmul := invCut_mul_self (χ := χ) (hIccne x hx) (hIccone x hx)
      calc (θ : ℝ → ℂ) x * invCut χ x * (x : ℂ)
          = (θ : ℝ → ℂ) x * (invCut χ x * (x : ℂ)) := by ring
        _ = (θ : ℝ → ℂ) x := by rw [hmul, mul_one]
    · rw [hθ x hx, zero_mul, zero_mul]
  -- the conjugated equation
  have hEq' : ∀ ψ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) →
      u (SchwartzMap.derivCLM ℂ ℂ ψ) = -(A (u ψ)) - u (mulTemperateCLM hm ψ) := by
    intro ψ hψ
    have hψIcc : ∀ x, x ∉ Icc a b → (ψ : ℝ → ℂ) x = 0 := fun x hx =>
      hψ x fun hc => hx (Ioo_subset_Icc_self hc)
    have hψ' : ∀ x, x ∉ Icc a b → deriv (ψ : ℝ → ℂ) x = 0 := by
      intro x hx
      have h := iteratedDeriv_eq_zero_of_notMem_Icc (ψ := ψ) hψ 1 hx
      rwa [iteratedDeriv_one] at h
    have hψ'supp : ∀ x, x ∉ Icc a b →
        ((SchwartzMap.derivCLM ℂ ℂ ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := hψ'
    have hφsupp : ∀ x, x ∉ Ioo a b →
        ((mulTemperateCLM hinv ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 :=
      mulTemperateCLM_eq_zero_of_notMem hinv hψ
    have hφIcc : ∀ x, x ∉ Icc a b →
        ((mulTemperateCLM hinv ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := fun x hx => by
      rw [mulTemperateCLM_apply, hψIcc x hx, zero_mul]
    -- the coordinate-divided test function
    have hgd : ∀ x ∈ Ioo a b, deriv (invCut χ) x = -(invCut χ x * invCut χ x) := by
      intro x hx
      exact deriv_invCut (hIccne x (Ioo_subset_Icc_self hx))
        (hUnhds x (Ioo_subset_Icc_self hx))
    have hleib := derivCLM_mulTemperateCLM hinv hinv hgd hψ
    have hcoordDeriv : coordMulCLM (SchwartzMap.derivCLM ℂ ℂ (mulTemperateCLM hinv ψ))
        = SchwartzMap.derivCLM ℂ ℂ ψ - mulTemperateCLM hinv ψ := by
      rw [hleib, map_sub, hdiv _ hψ'supp, hdiv _ hφIcc]
    have hcoord : coordMulCLM (mulTemperateCLM hinv ψ) = ψ := hdiv ψ hψIcc
    have hmulq : mulTemperateCLM hq (mulTemperateCLM hinv ψ) = mulTemperateCLM hrcut ψ := by
      refine SchwartzMap.ext fun x => ?_
      rw [mulTemperateCLM_apply, mulTemperateCLM_apply, mulTemperateCLM_apply]
      by_cases hx : x ∈ Icc a b
      · have hmul := invCut_mul_self (χ := χ) (hIccne x hx) (hIccone x hx)
        have hone : χ x = 1 := hIccone x hx
        push_cast [hone]
        calc (ψ : ℝ → ℂ) x * invCut χ x * ((x : ℂ) * ((r x : ℝ) : ℂ))
            = (ψ : ℝ → ℂ) x * (invCut χ x * (x : ℂ)) * ((r x : ℝ) : ℂ) := by ring
          _ = (ψ : ℝ → ℂ) x * (1 * ((r x : ℝ) : ℂ)) := by rw [hmul]; ring
      · rw [hψIcc x hx, zero_mul, zero_mul, zero_mul]
    have hmsplit : mulTemperateCLM hm ψ
        = (-(1 : ℂ) / 2) • mulTemperateCLM hinv ψ + (I / 2) • mulTemperateCLM hrcut ψ := by
      refine SchwartzMap.ext fun x => ?_
      show (ψ : ℝ → ℂ) x * gammaMultiplier χ r x
        = (-(1 : ℂ) / 2) * ((ψ : ℝ → ℂ) x * invCut χ x)
          + (I / 2) * ((ψ : ℝ → ℂ) x * ((χ x * r x : ℝ) : ℂ))
      rw [gammaMultiplier]
      ring
    have hbase := hEq (mulTemperateCLM hinv ψ) hφsupp
    rw [hcoordDeriv, hcoord, hmulq, map_sub] at hbase
    have hAval : -(A (u ψ)) = (I / 2) • T (u ψ) := by
      rw [hA, smul_apply, ← neg_smul]
      congr 1
      ring
    have hmval : u (mulTemperateCLM hm ψ)
        = (-(1 : ℂ) / 2) • u (mulTemperateCLM hinv ψ) + (I / 2) • u (mulTemperateCLM hrcut ψ) := by
      rw [hmsplit, map_add, map_smul, map_smul]
    rw [hAval, hmval]
    have hne : (2 : ℂ) ≠ 0 := by norm_num
    refine smul_right_injective X hne ?_
    show (2 : ℂ) • u (SchwartzMap.derivCLM ℂ ℂ ψ)
      = (2 : ℂ) • ((I / 2) • T (u ψ)
          - ((-(1 : ℂ) / 2) • u (mulTemperateCLM hinv ψ)
            + (I / 2) • u (mulTemperateCLM hrcut ψ)))
    linear_combination (norm := module) hbase
  -- the integrating-factor identities
  have hgderiv : ∀ x ∈ Ioo a b,
      deriv (sqrtFactor χ Rint) x = -(gammaMultiplier χ r x * sqrtFactor χ Rint x) := by
    intro x hx
    exact deriv_sqrtFactor (hIccne x (Ioo_subset_Icc_self hx))
      (hUnhds x (Ioo_subset_Icc_self hx)) hRderiv
  have hgprod : ∀ x ∈ Ioo a b, sqrtFactor χ Rint x * sqrtFactorInv χ Rint x = 1 := by
    intro x hx
    exact sqrtFactor_mul_inv (hIccne x (Ioo_subset_Icc_self hx))
      (hIccone x (Ioo_subset_Icc_self hx))
  obtain ⟨c, hc⟩ :=
    exists_conjugate_representation A u hab hm hgfac hginv hgderiv hgprod hEq'
  refine ⟨c, fun φ hsupp => ?_⟩
  rw [hc φ hsupp]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have htIcc : t ∈ Icc a b := by rwa [uIcc_of_le hab.le] at ht
  have htne : t ≠ 0 := hIccne t htIcc
  have hone : χ t = 1 := hIccone t htIcc
  have hsqrt : ((Real.sqrt |t| : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr htne))
  -- the propagator identification
  have hopPhase : NormedSpace.exp ((t : ℂ) • A) = opPhase T t := by
    have harg : ((t : ℂ) • A) = t • ((-I / 2 : ℂ) • T) := by
      rw [hA, smul_smul, ← smul_assoc, Complex.real_smul]
    rw [harg]
    rfl
  have hphase : gammaPhase 0 Rint t = Complex.exp ((I / 2) * ((Rint t : ℝ) : ℂ)) := by
    rw [gammaPhase]
    congr 1
    push_cast
    ring
  have hrpow : (|t| ^ (-(1 : ℝ) / 2) : ℝ) = (Real.sqrt |t|)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg t)]
    norm_num
  have hsmulReal : ∀ (v : X), (|t| ^ (-(1 : ℝ) / 2) : ℝ) • v
      = ((((Real.sqrt |t| : ℝ) : ℂ))⁻¹) • v := by
    intro v
    rw [hrpow, ← ofReal_smul_eq ((Real.sqrt |t|)⁻¹) v]
    congr 1
    push_cast
    ring
  have hgt : gammaTransport Rint T t c
      = Complex.exp ((I / 2) * ((Rint t : ℝ) : ℂ)) • (NormedSpace.exp ((t : ℂ) • A) c) := by
    rw [gammaTransport, freqPropagator, smul_apply, hphase, ← hopPhase]
  rw [gammaFrequencyProfile, hgt, hsmulReal]
  simp only [smul_smul]
  congr 1
  rw [sqrtFactorInv, hone]
  push_cast
  ring

/-- The Gamma transport is continuous in the frequency. -/
theorem continuous_gammaTransport {Rint r : ℝ → ℝ} (T : X →L[ℂ] X)
    (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x) :
    Continuous (fun t : ℝ => gammaTransport Rint T t) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_freqPropagator (L := 0) T (hRderiv t)).continuousAt

/-- The Gamma profile is continuous away from the origin. -/
theorem continuousOn_gammaFrequencyProfile {Rint r : ℝ → ℝ} (T : X →L[ℂ] X) (c : X)
    (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x) {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (gammaFrequencyProfile Rint T c) s := by
  have h1 : ContinuousOn (fun t : ℝ => (|t| ^ (-(1 : ℝ) / 2) : ℝ)) s :=
    (continuous_abs.continuousOn).rpow_const fun x hx => Or.inl (abs_ne_zero.mpr (hs x hx))
  have h2 : Continuous (fun t : ℝ => gammaTransport Rint T t c) :=
    ((ContinuousLinearMap.apply ℂ X c).continuous).comp (continuous_gammaTransport T hRderiv)
  exact h1.smul h2.continuousOn

omit [CompleteSpace X] in
/-- An interval integral of a function carried by a subinterval is the integral over that
subinterval. -/
theorem intervalIntegral_eq_of_subset {f : ℝ → X} {a b a' b' : ℝ}
    (hab : a ≤ b) (h1 : a' ≤ a) (h2 : b ≤ b') (hf : ∀ x, x ∉ Ioo a b → f x = 0) :
    (∫ t in a'..b', f t) = ∫ t in a..b, f t := by
  have hab' : a' ≤ b' := le_trans h1 (le_trans hab h2)
  rw [intervalIntegral.integral_of_le hab', intervalIntegral.integral_of_le hab]
  refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc h1 h2) fun x hx => ?_
  exact hf x fun hc => hx.2 (Ioo_subset_Ioc_self hc)

/-- **The distributional channel vector is unique.** -/
theorem channel_vector_unique_distributional {Rint r : ℝ → ℝ} (T : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    {a b : ℝ} (hab : a < b) (h0 : (0 : ℝ) ∉ Icc a b)
    (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x) {c c' : X}
    (hc : ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c t)
    (hc' : ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c' t) :
    c = c' := by
  have hne : ∀ x ∈ Icc a b, x ≠ 0 := by
    intro x hx hcon
    exact h0 (hcon ▸ hx)
  have hcont : ContinuousOn (fun t : ℝ => gammaFrequencyProfile Rint T c t - gammaFrequencyProfile Rint T c' t)
      (Icc a b) :=
    (continuousOn_gammaFrequencyProfile T c hRderiv hne).sub (continuousOn_gammaFrequencyProfile T c' hRderiv hne)
  have hzero : ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      (∫ t in a..b, ((φ : ℝ → ℂ) t)
        • (gammaFrequencyProfile Rint T c t - gammaFrequencyProfile Rint T c' t)) = 0 := by
    intro φ hφ
    have hi1 : IntervalIntegrable
        (fun t : ℝ => ((φ : ℝ → ℂ) t) • gammaFrequencyProfile Rint T c t) MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab.le]
      exact (φ.continuous.continuousOn).smul (continuousOn_gammaFrequencyProfile T c hRderiv hne)
    have hi2 : IntervalIntegrable
        (fun t : ℝ => ((φ : ℝ → ℂ) t) • gammaFrequencyProfile Rint T c' t) MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab.le]
      exact (φ.continuous.continuousOn).smul (continuousOn_gammaFrequencyProfile T c' hRderiv hne)
    have hsplit : (fun t : ℝ => ((φ : ℝ → ℂ) t)
        • (gammaFrequencyProfile Rint T c t - gammaFrequencyProfile Rint T c' t))
        = fun t : ℝ => ((φ : ℝ → ℂ) t) • gammaFrequencyProfile Rint T c t
          - ((φ : ℝ → ℂ) t) • gammaFrequencyProfile Rint T c' t := by
      funext t
      rw [smul_sub]
    rw [hsplit, intervalIntegral.integral_sub hi1 hi2, ← hc φ hφ, ← hc' φ hφ, sub_self]
  have hvanish := eq_zero_of_forall_test_integral_zero hab hcont hzero
  obtain ⟨t₀, ht₀⟩ : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
  have hG := hvanish t₀ ht₀
  have ht₀ne : t₀ ≠ 0 := hne t₀ (Ioo_subset_Icc_self ht₀)
  have hdiff : (|t₀| ^ (-(1 : ℝ) / 2)) • (gammaTransport Rint T t₀ (c - c')) = 0 := by
    rw [map_sub, smul_sub]
    exact hG
  have hscal : (|t₀| ^ (-(1 : ℝ) / 2) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < |t₀| := abs_pos.mpr ht₀ne
    positivity
  have hzeroQ : gammaTransport Rint T t₀ (c - c') = 0 :=
    (smul_eq_zero.mp hdiff).resolve_left hscal
  have hinv := gammaTransportInv_mul (Rint := Rint) (T := T) t₀
  have happ : gammaTransportInv Rint T t₀ (gammaTransport Rint T t₀ (c - c')) = c - c' := by
    show (gammaTransportInv Rint T t₀ * gammaTransport Rint T t₀) (c - c') = c - c'
    rw [hinv]
    rfl
  rw [hzeroQ, map_zero] at happ
  exact sub_eq_zero.mp happ.symm

/-- **The classification on the whole positive frequency half-line.**  One channel vector serves
every compact subinterval. -/
theorem exists_channel_vector_positive (T : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    {Rint r : ℝ → ℝ}
    (hRint : ContDiff ℝ (⊤ : ℕ∞) Rint) (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hq : Function.HasTemperateGrowth (fun x : ℝ => ((x * r x : ℝ) : ℂ)))
    (hEq : ∀ φ : SchwartzMap ℝ ℂ,
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ))
        + I • u (mulTemperateCLM hq φ) - I • T (u (coordMulCLM φ)) = 0) :
    ∃ c : X, ∀ a b : ℝ, 0 < a → a < b → ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
        u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c t := by
  have key : ∀ a b : ℝ, 0 < a → a < b → ∃ c : X, ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
        u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c t := by
    intro a b ha hab
    have h0 : (0 : ℝ) ∉ Icc a b := by
      intro hc
      exact absurd hc.1 (not_le.mpr ha)
    exact exists_channel_vector_distributional T u hab h0 hRint hRderiv hq
      (fun φ _ => hEq φ)
  obtain ⟨c₀, hc₀⟩ := key (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨c₀, fun a b ha hab φ hφ => ?_⟩
  set a' : ℝ := min a (1 / 2) with ha'
  set b' : ℝ := max b 2 with hb'
  have ha'pos : 0 < a' := lt_min ha (by norm_num)
  have ha'b' : a' < b' := by
    have h1 : a' ≤ a := min_le_left _ _
    have h2 : b ≤ b' := le_max_left _ _
    linarith
  obtain ⟨c₁, hc₁⟩ := key a' b' ha'pos ha'b'
  have h0' : (0 : ℝ) ∉ Icc (1 / 2 : ℝ) 2 := by
    intro hc
    have := hc.1
    norm_num at this
  have hrestrict : ∀ (x y : ℝ), a' ≤ x → y ≤ b' → x ≤ y → ∀ ψ : SchwartzMap ℝ ℂ,
      (∀ z, z ∉ Ioo x y → (ψ : ℝ → ℂ) z = 0) →
        u ψ = ∫ t in x..y, (ψ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c₁ t := by
    intro x y hx hy hxy ψ hψ
    have hsupp : ∀ z, z ∉ Ioo x y → ((ψ : ℝ → ℂ) z) • gammaFrequencyProfile Rint T c₁ z = 0 := by
      intro z hz
      rw [hψ z hz, zero_smul]
    have hψ' : ∀ z, z ∉ Ioo a' b' → (ψ : ℝ → ℂ) z = 0 := by
      intro z hz
      refine hψ z fun hc => hz ⟨lt_of_le_of_lt hx hc.1, lt_of_lt_of_le hc.2 hy⟩
    rw [hc₁ ψ hψ', intervalIntegral_eq_of_subset hxy hx hy hsupp]
  have heq₀ : c₀ = c₁ := by
    refine channel_vector_unique_distributional T u (by norm_num : (1 / 2 : ℝ) < 2) h0' hRderiv
      hc₀ ?_
    intro ψ hψ
    exact hrestrict (1 / 2) 2 (min_le_right _ _) (le_max_right _ _) (by norm_num) ψ hψ
  rw [heq₀]
  exact hrestrict a b (min_le_left _ _) (le_max_left _ _) hab.le φ hφ

/-- **The classification on the whole negative frequency half-line.** -/
theorem exists_channel_vector_negative (T : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    {Rint r : ℝ → ℝ}
    (hRint : ContDiff ℝ (⊤ : ℕ∞) Rint) (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hq : Function.HasTemperateGrowth (fun x : ℝ => ((x * r x : ℝ) : ℂ)))
    (hEq : ∀ φ : SchwartzMap ℝ ℂ,
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ))
        + I • u (mulTemperateCLM hq φ) - I • T (u (coordMulCLM φ)) = 0) :
    ∃ c : X, ∀ a b : ℝ, b < 0 → a < b → ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
        u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c t := by
  have key : ∀ a b : ℝ, b < 0 → a < b → ∃ c : X, ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
        u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c t := by
    intro a b hb hab
    have h0 : (0 : ℝ) ∉ Icc a b := by
      intro hc
      exact absurd hc.2 (not_le.mpr hb)
    exact exists_channel_vector_distributional T u hab h0 hRint hRderiv hq (fun φ _ => hEq φ)
  obtain ⟨c₀, hc₀⟩ := key (-2) (-(1 / 2)) (by norm_num) (by norm_num)
  refine ⟨c₀, fun a b hb hab φ hφ => ?_⟩
  set a' : ℝ := min a (-2) with ha'
  set b' : ℝ := max b (-(1 / 2)) with hb'
  have hb'neg : b' < 0 := max_lt hb (by norm_num)
  have ha'b' : a' < b' := by
    have h1 : a' ≤ a := min_le_left _ _
    have h2 : b ≤ b' := le_max_left _ _
    linarith
  obtain ⟨c₁, hc₁⟩ := key a' b' hb'neg ha'b'
  have h0' : (0 : ℝ) ∉ Icc (-2 : ℝ) (-(1 / 2)) := by
    intro hc
    have := hc.2
    norm_num at this
  have hrestrict : ∀ (x y : ℝ), a' ≤ x → y ≤ b' → x ≤ y → ∀ ψ : SchwartzMap ℝ ℂ,
      (∀ z, z ∉ Ioo x y → (ψ : ℝ → ℂ) z = 0) →
        u ψ = ∫ t in x..y, (ψ : ℝ → ℂ) t • gammaFrequencyProfile Rint T c₁ t := by
    intro x y hx hy hxy ψ hψ
    have hsupp : ∀ z, z ∉ Ioo x y → ((ψ : ℝ → ℂ) z) • gammaFrequencyProfile Rint T c₁ z = 0 := by
      intro z hz
      rw [hψ z hz, zero_smul]
    have hψ' : ∀ z, z ∉ Ioo a' b' → (ψ : ℝ → ℂ) z = 0 := by
      intro z hz
      refine hψ z fun hc => hz ⟨lt_of_le_of_lt hx hc.1, lt_of_lt_of_le hc.2 hy⟩
    rw [hc₁ ψ hψ', intervalIntegral_eq_of_subset hxy hx hy hsupp]
  have heq₀ : c₀ = c₁ := by
    refine channel_vector_unique_distributional T u (by norm_num : (-2 : ℝ) < -(1 / 2)) h0'
      hRderiv hc₀ ?_
    intro ψ hψ
    exact hrestrict (-2) (-(1 / 2)) (min_le_right _ _) (le_max_right _ _) (by norm_num) ψ hψ
  rw [heq₀]
  exact hrestrict a b (min_le_left _ _) (le_max_left _ _) hab.le φ hφ

/-- **The homogeneous Gamma classification.**  A tempered distributional solution of the Gamma
frequency equation is, on each open frequency half-line, the Gamma transport applied to a single
channel vector, and no nonzero solution is supported at the origin. -/
theorem gamma_tempered_classification (T : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    {Rint r : ℝ → ℝ}
    (hRint : ContDiff ℝ (⊤ : ℕ∞) Rint) (hRderiv : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hq : Function.HasTemperateGrowth (fun x : ℝ => ((x * r x : ℝ) : ℂ)))
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (hEq : ∀ φ : SchwartzMap ℝ ℂ,
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ))
        + I • u (mulTemperateCLM hq φ) - I • T (u (coordMulCLM φ)) = 0) :
    (∃ cpos : X, ∀ a b : ℝ, 0 < a → a < b → ∀ φ : SchwartzMap ℝ ℂ,
        (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
          u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T cpos t)
      ∧ (∃ cneg : X, ∀ a b : ℝ, b < 0 → a < b → ∀ φ : SchwartzMap ℝ ℂ,
        (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
          u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • gammaFrequencyProfile Rint T cneg t)
      ∧ ((∀ ψ : SchwartzMap ℝ ℂ, (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → (ψ : ℝ → ℂ) x = 0) → u ψ = 0) →
          ∀ φ : SchwartzMap ℝ ℂ, u φ = 0) := by
  refine ⟨exists_channel_vector_positive T u hRint hRderiv hq hEq,
    exists_channel_vector_negative T u hRint hRderiv hq hEq, fun hu => ?_⟩
  have hgc : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((x * r x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.mul hr)
  have hg0 : ((0 * r 0 : ℝ) : ℂ) = 0 := by simp
  exact eq_zero_of_pointSupport_gammaForm hq hgc hg0 T hu hEq

end

end GaloisForLFunctions.RHTower
