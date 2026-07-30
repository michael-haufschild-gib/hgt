import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.SeamFluxCompletion

/-!
# Fixed cross-order reflection of the removable completed-flux germ

The completed flux `-ξ'/ξ` is meromorphic at a zero, but multiplication by the local coordinate
removes its pole.  Filling the center with the negative vanishing order gives one canonical analytic
germ at every point.  Functional-equation reciprocity identifies the germ at `1-ρ`, in its
reflected local coordinate, with the germ at `ρ`.  Consequently the same infinite Taylor sequence
obeys FE parity at every order; no finite packet, cutoff, or order-dependent interpolation occurs.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The completed local flux germ.  Away from the center it is `x(-ξ'/ξ)(ρ+x)`; at the
center it is filled by its removable value `-ord_ρ(ξ)`. -/
def completedFluxGermAt (ρ x : ℂ) : ℂ :=
  if x = 0 then -((analyticOrderAt xi ρ).toNat : ℂ)
  else x * seamFluxCochain (ρ + x)

@[simp] theorem completedFluxGermAt_zero (ρ : ℂ) :
    completedFluxGermAt ρ 0 = -((analyticOrderAt xi ρ).toNat : ℂ) := by
  simp [completedFluxGermAt]

/-- Pointwise FE law in reflected local coordinates. -/
theorem completedFluxGermAt_reflection (ρ x : ℂ) :
    completedFluxGermAt (1 - ρ) (-x) = completedFluxGermAt ρ x := by
  by_cases hx : x = 0
  · subst x
    simp [xi_orderAt_one_sub]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [completedFluxGermAt, if_neg hnx, completedFluxGermAt, if_neg hx]
    rw [show (1 - ρ) + -x = 1 - (ρ + x) by ring,
      seamFluxCochain_reciprocity]
    ring

/-- The residue-filled completed flux is genuinely analytic at the local origin. -/
theorem completedFluxGermAt_analyticAt_zero (ρ : ℂ) :
    AnalyticAt ℂ (completedFluxGermAt ρ) 0 := by
  obtain ⟨R, hR, h, hhan, hh0, hlocal⟩ :=
    exists_xi_normalizedLogDeriv_factorization ρ
  have hρball : ρ ∈ ball ρ R := mem_ball_self hR
  have hha : AnalyticAt ℂ h ρ := hhan ρ hρball
  have hlog : AnalyticAt ℂ (logDeriv h) ρ := by
    rw [show logDeriv h = fun z => deriv h z / h z by
      funext z
      rw [logDeriv_apply]]
    exact hha.deriv.div hha (hh0 ρ hρball)
  have hshift : AnalyticAt ℂ (fun x : ℂ => logDeriv h (ρ + x)) 0 := by
    have hcomp := AnalyticAt.comp_of_eq hlog
      (show AnalyticAt ℂ (fun x : ℂ => ρ + x) 0 by fun_prop) (by simp)
    simpa [Function.comp] using! hcomp
  have hmodel : AnalyticAt ℂ
      (fun x : ℂ => -((analyticOrderAt xi ρ).toNat : ℂ) -
        x * logDeriv h (ρ + x)) 0 := by
    exact analyticAt_const.sub (analyticAt_id.mul hshift)
  apply hmodel.congr
  have hshiftTendsto : Tendsto (fun x : ℂ => ρ + x) (nhds 0) (nhds ρ) := by
    have hc : Continuous (fun x : ℂ => ρ + x) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hball : ∀ᶠ x : ℂ in nhds 0, ρ + x ∈ ball ρ R :=
    hshiftTendsto (isOpen_ball.mem_nhds hρball)
  filter_upwards [hball] with x hxball
  by_cases hx : x = 0
  · subst x
    simp
  · rw [completedFluxGermAt, if_neg hx, seamFluxCochain]
    have hzne : ρ + x ≠ ρ := by simpa using hx
    have hfactor := hlocal (ρ + x) hxball hzne
    simp only [add_sub_cancel_left] at hfactor
    calc
      -((analyticOrderAt xi ρ).toNat : ℂ) - x * logDeriv h (ρ + x) =
          -(((analyticOrderAt xi ρ).toNat : ℂ) + x * logDeriv h (ρ + x)) := by ring
      _ = -(x * logDeriv xi (ρ + x)) := by rw [← hfactor]
      _ = x * -logDeriv xi (ρ + x) := by ring

/-- The single, order-independent Taylor coefficient sequence of the completed local flux. -/
def completedFluxTaylorCoeff (ρ : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (completedFluxGermAt ρ) 0 / n.factorial

/-- All-order FE parity: paired coefficients differ by the forced sign `(-1)^n`. -/
theorem completedFluxTaylorCoeff_reflection (ρ : ℂ) (n : ℕ) :
    (-1 : ℂ) ^ n * completedFluxTaylorCoeff (1 - ρ) n =
      completedFluxTaylorCoeff ρ n := by
  have hfun : (fun x : ℂ => completedFluxGermAt (1 - ρ) (-x)) =
      completedFluxGermAt ρ := by
    funext x
    exact completedFluxGermAt_reflection ρ x
  have hder := congrArg (fun f : ℂ → ℂ => iteratedDeriv n f 0) hfun
  change iteratedDeriv n (fun x : ℂ => completedFluxGermAt (1 - ρ) (-x)) 0 =
    iteratedDeriv n (completedFluxGermAt ρ) 0 at hder
  rw [iteratedDeriv_comp_neg] at hder
  simp only [neg_zero, smul_eq_mul] at hder
  rw [completedFluxTaylorCoeff, completedFluxTaylorCoeff]
  calc
    (-1 : ℂ) ^ n * (iteratedDeriv n (completedFluxGermAt (1 - ρ)) 0 / n.factorial) =
        (((-1 : ℂ) ^ n * iteratedDeriv n (completedFluxGermAt (1 - ρ)) 0) /
          n.factorial) := by ring
    _ = iteratedDeriv n (completedFluxGermAt ρ) 0 / n.factorial := by rw [hder]

/-- At the FE fixed point, every odd coefficient of the completed-flux germ vanishes. -/
theorem completedFluxTaylorCoeff_central_odd_eq_zero {n : ℕ} (hn : Odd n) :
    completedFluxTaylorCoeff (1 / 2 : ℂ) n = 0 := by
  have hpar := completedFluxTaylorCoeff_reflection (1 / 2 : ℂ) n
  rw [show 1 - (1 / 2 : ℂ) = 1 / 2 by ring, hn.neg_one_pow] at hpar
  have hneg : -completedFluxTaylorCoeff (1 / 2 : ℂ) n =
      completedFluxTaylorCoeff (1 / 2 : ℂ) n := by simpa using hpar
  have hsum : completedFluxTaylorCoeff (1 / 2 : ℂ) n +
      completedFluxTaylorCoeff (1 / 2 : ℂ) n = 0 := by
    calc
      completedFluxTaylorCoeff (1 / 2 : ℂ) n +
          completedFluxTaylorCoeff (1 / 2 : ℂ) n =
        completedFluxTaylorCoeff (1 / 2 : ℂ) n +
          -completedFluxTaylorCoeff (1 / 2 : ℂ) n := by rw [hneg]
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℂ) * completedFluxTaylorCoeff (1 / 2 : ℂ) n = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end

end RHTower
