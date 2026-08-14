import GaloisForLFunctions.HTGeometry.ConjugatedTransportRepresentation
import GaloisForLFunctions.HTGeometry.HalfLineIntegratingFactor
import GaloisForLFunctions.RHTower.SuzukiGammaHalfLineClassification

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
      u φ = ∫ t in a..b, (φ : ℝ → ℂ) t
        • ((|t| ^ (-(1 : ℝ) / 2)) • gammaTransport Rint T t c) := by
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
  rw [hgt, hsmulReal]
  simp only [smul_smul]
  congr 1
  rw [sqrtFactorInv, hone]
  push_cast
  ring

end

end GaloisForLFunctions.RHTower
