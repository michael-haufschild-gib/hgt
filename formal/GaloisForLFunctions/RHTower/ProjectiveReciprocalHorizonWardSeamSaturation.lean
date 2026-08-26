import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetTailTransition
import GaloisForLFunctions.RHTower.MobiusSquarefreeReciprocalProjectivePaperCertificate
import GaloisForLFunctions.RHTower.CCMBoundaryRelativeTrace

/-!
# Saturation of the reciprocal projective-horizon Ward seam

This capstone assembles the exact projective, squarefree-source, divisor, and boundary-trace
statements of the projective reciprocal-horizon Ward-seam card.  The source connection is the
literal completed squarefree current; no divisor list is used to define it.
-/

open Complex Filter Set
open scoped Differential Topology

namespace GaloisForLFunctions

noncomputable section

/-- The complete generic HT reciprocal-horizon package: reciprocal-square transition, its
logarithmic connection, and the sharp depth-one/depth-two fixed-field transition. -/
theorem hypertranscendentalOver_projectiveReciprocalWardSeam_complete
    {C E : Type*} [Field C] [CharZero C] [Differential C]
    [Field E] [CharZero E] [Algebra C E] [Differential E]
    [DifferentialAlgebra C E]
    (x : E) (hx : HypertranscendentalOver C x) :
    (x⁻¹)′ / x′ = -x⁻¹ ^ 2 ∧
      (x⁻¹)′′ / (x⁻¹)′ - x′′ / x′ = -2 * (x′ / x) ∧
      (jetTailField C x 1 ⊓ jetTailField C x⁻¹ 1 ≠ ⊥ ∧
        ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → (2 ≤ m ∨ 2 ≤ n) →
          jetTailField C x m ⊓ jetTailField C x⁻¹ n = ⊥) := by
  exact ⟨hypertranscendentalOver_projectiveHorizon_reciprocalTransition x hx,
    hypertranscendentalOver_projectiveHorizon_reciprocalConnection x hx,
    hypertranscendentalOver_projectiveHorizon_sharpDepthTransition x hx⟩

end

end GaloisForLFunctions

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- A complex analytic zero of exact finite order has logarithmic residue equal to that order. -/
theorem AnalyticAt.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast_complex
    {f : ℂ → ℂ} {x : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = d) :
    Tendsto (fun w => (w - x) * logDeriv f w)
      (𝓝[≠] x) (𝓝 (d : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp horder
  have hfgEq : f =ᶠ[𝓝 x] (fun z => (z - x) ^ d * g z) := by
    filter_upwards [hfg] with z hz
    simpa only [smul_eq_mul] using hz
  have hgNonzero : ∀ᶠ w in 𝓝 x, g w ≠ 0 :=
    hg.continuousAt.tendsto.eventually_ne hg0
  have hgAnalytic : ∀ᶠ w in 𝓝 x, AnalyticAt ℂ g w := hg.eventually_analyticAt
  have hlog : ∀ᶠ w in 𝓝[≠] x,
      logDeriv f w = (d : ℂ) / (w - x) + logDeriv g w := by
    filter_upwards [hfgEq.filter_mono nhdsWithin_le_nhds,
      hfgEq.deriv.filter_mono nhdsWithin_le_nhds,
      hgNonzero.filter_mono nhdsWithin_le_nhds,
      hgAnalytic.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hfw hdfw hgw hga hw
    have hwx : w ≠ x := by simpa using hw
    have hpow : (w - x) ^ d ≠ 0 := pow_ne_zero d (sub_ne_zero.mpr hwx)
    have hmul := logDeriv_mul (f := fun z : ℂ => (z - x) ^ d) (g := g)
      w hpow hgw (by fun_prop) hga.differentiableAt
    rw [logDeriv_apply, hdfw, hfw]
    rw [← logDeriv_apply, hmul, logDeriv_fun_pow (by fun_prop) d]
    have hlinear : logDeriv (fun z : ℂ => z - x) w = 1 / (w - x) := by
      simp [logDeriv_apply]
    rw [hlinear]
    ring
  have hlogContinuous : ContinuousAt (logDeriv g) x := by
    change ContinuousAt (deriv g / g) x
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have hsub : Tendsto (fun w : ℂ => w - x) (𝓝[≠] x) (𝓝 0) := by
    have h : ContinuousAt (fun w : ℂ => w - x) x :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hrem : Tendsto (fun w : ℂ => (w - x) * logDeriv g w)
      (𝓝[≠] x) (𝓝 0) := by
    convert hsub.mul (hlogContinuous.tendsto.mono_left nhdsWithin_le_nhds) using 1
    all_goals simp
  rw [tendsto_congr' (show
    (fun w : ℂ => (w - x) * logDeriv f w) =ᶠ[𝓝[≠] x]
      (fun w => (d : ℂ) + (w - x) * logDeriv g w) by
        filter_upwards [hlog, self_mem_nhdsWithin] with w hw hne
        have hwx : w ≠ x := by simpa using hne
        rw [hw]
        field_simp [sub_ne_zero.mpr hwx])]
  simpa using tendsto_const_nhds.add hrem

/-- The completed squarefree source and the completed Möbius transfer have the same literal Ward
connection on the Euler half-plane, with the reciprocal-source sign convention of the card. -/
theorem completedSquarefreePartition_projectiveReciprocalWardSeam
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ∀ s : ℂ, 1 < s.re →
      (-2 * logDeriv completedSquarefreePartition s =
          completedSquarefreeFixedCurrent s ∧
        2 * logDeriv (mobiusCompletedSquarefreeTransfer sigma) s =
          completedSquarefreeFixedCurrent s) := by
  intro s hs
  exact ⟨neg_two_mul_logDeriv_completedSquarefreePartition hs,
    two_mul_logDeriv_mobiusCompletedSquarefreeTransfer hsigma hs⟩

/-- Every observer depending only on the Euler-half-plane connection reads exactly the completed
squarefree Ward current from the completed reciprocal transfer.  This includes the anti-causal
Hardy observer used in the card. -/
theorem completedSquarefreePartition_projectiveReciprocalWardObserver
    {alpha : Type*} {sigma : ℝ} (hsigma : 1 < sigma)
    (P : (ℂ → ℂ) → alpha)
    (hP : ∀ F G : ℂ → ℂ, EqOn F G {s : ℂ | 1 < s.re} → P F = P G) :
    P (fun s => 2 * logDeriv (mobiusCompletedSquarefreeTransfer sigma) s) =
      P completedSquarefreeFixedCurrent :=
  mobiusCompletedSquarefreeTransfer_connection_transport hsigma P hP

/-- The completed squarefree chart carries exactly the complete Xi divisor order throughout the
strict-right open critical half-strip. -/
theorem analyticOrderAt_completedSquarefreePartition_eq_xi_of_strictRightStrip
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (_hone : rho.re < 1) :
    analyticOrderAt completedSquarefreePartition rho = analyticOrderAt xi rho := by
  have htwoRe : 1 < (2 * rho).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have htwoOne : 2 * rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, one_re] at hre
    linarith
  have hxi : AnalyticAt ℂ xi rho := xi_analyticOnNhd_univ rho (Set.mem_univ rho)
  have hden : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) rho :=
    (analyticOn_riemannZeta (2 * rho) htwoOne).comp
      (show AnalyticAt ℂ (fun z : ℂ => 2 * z) rho by fun_prop)
  have hden0 : riemannZeta (2 * rho) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoRe
  have hinv : AnalyticAt ℂ (fun z : ℂ => (riemannZeta (2 * z))⁻¹) rho :=
    hden.inv hden0
  change analyticOrderAt (xi * fun z : ℂ => (riemannZeta (2 * z))⁻¹) rho = _
  rw [analyticOrderAt_mul hxi hinv,
    hinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero hden0), add_zero]

/-- A strict-right Xi zero is a puncture of the reciprocal projective transition with charge
`-2m`, where `m` is its complete analytic multiplicity. -/
theorem completedSquarefreePartition_projectivePunctureCharge
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - rho) * (-2 * logDeriv completedSquarefreePartition s))
        (𝓝[≠] rho) (𝓝 (-2 * (m : ℂ))) := by
  let m : ℕ := (analyticOrderAt xi rho).toNat
  have hxi : AnalyticAt ℂ xi rho := xi_analyticOnNhd_univ rho (Set.mem_univ rho)
  have hordFinite : analyticOrderAt xi rho ≠ ⊤ := xi_order_ne_top rho
  have hmne : m ≠ 0 := by
    intro hm
    rcases ENat.toNat_eq_zero.mp hm with hord0 | hordTop
    · exact (analyticOrderAt_ne_zero.mpr ⟨hxi, hzero⟩) hord0
    · exact hordFinite hordTop
  have htwoRe : 1 < (2 * rho).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have htwoOne : 2 * rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, one_re] at hre
    linarith
  have hden : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) rho :=
    (analyticOn_riemannZeta (2 * rho) htwoOne).comp
      (show AnalyticAt ℂ (fun z : ℂ => 2 * z) rho by fun_prop)
  have hden0 : riemannZeta (2 * rho) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoRe
  have hsource : AnalyticAt ℂ completedSquarefreePartition rho := by
    change AnalyticAt ℂ (fun z : ℂ => xi z / riemannZeta (2 * z)) rho
    exact hxi.div hden hden0
  have hord : analyticOrderAt completedSquarefreePartition rho = (m : ℕ∞) := by
    rw [analyticOrderAt_completedSquarefreePartition_eq_xi_of_strictRightStrip hhalf hone]
    exact (ENat.coe_toNat hordFinite).symm
  have hres :=
    RHTower.AnalyticAt.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast_complex
      hsource hord
  refine ⟨m, Nat.one_le_iff_ne_zero.mpr hmne, ?_⟩
  convert tendsto_const_nhds.mul hres using 1 <;> ring

end


end RHTower

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exact positive boundary trace of every finite strict-right divisor packet.  The initial trace
density is its complete Cauchy residue energy. -/
theorem completedSquarefree_boundaryTraceDensity
    {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    Tendsto (fun u : ℝ => boundaryRelativeTrace (divisorPacketProfile lam m) u / u)
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorPacketEnergy lam m)) :=
  tendsto_boundaryRelativeTrace_div_divisorPacket hlam

end


end GaloisForLFunctions.RHTower
