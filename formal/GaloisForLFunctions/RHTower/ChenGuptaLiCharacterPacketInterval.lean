/-
# Chen--Gupta--Li character-packet interval identity

Chen--Gupta--Li Lemma 9.1 turns the finite character packet

`R(v,a) = Σ_{(t,χ)∈W} v^{it}χ(a)`

into a second-moment integral over a compact `v`-range.  After `v = exp τ`,
this module proves the exact finite interval identity: character
orthogonality leaves only same-character pairs, weighted by their elementary
oscillatory interval kernel.  The following layer bounds that kernel using the
source's ordinate separation.

No RH, GRH, smoothness, separation, large-value, or zero-density premise is
used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterOrthogonality

open Complex MeasureTheory

noncomputable section

namespace RHTower

/-- The source wave `exp(i t τ)` is continuous in the log-ordinate `τ`. -/
theorem continuous_cglCharacterPacketWave (t : ℝ) :
    Continuous (fun τ : ℝ => cglCharacterPacketWave t τ) := by
  unfold cglCharacterPacketWave
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

/-- A literal finite CGL packet is continuous in its log-ordinate. -/
theorem continuous_cglCharacterPacket (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (a : ZMod (q + 1)) :
    Continuous (fun τ : ℝ => cglCharacterPacket q R w τ a) := by
  unfold cglCharacterPacket
  apply continuous_finsetSum Finset.univ
  intro r hr
  exact (continuous_cglCharacterPacketWave (w r).time).mul continuous_const

/-- The finite Hermitian packet mass is continuous, so every compact interval
integral in the CGL second-moment argument is defined without an auxiliary
integrability premise. -/
theorem continuous_cglCharacterPacketHermitianMass (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    Continuous (fun τ : ℝ => cglCharacterPacketHermitianMass q R w τ) := by
  unfold cglCharacterPacketHermitianMass
  apply continuous_finsetSum Finset.univ
  intro a ha
  exact (continuous_cglCharacterPacket q R w a).mul
    (Complex.continuous_conj.comp (continuous_cglCharacterPacket q R w a))

/-- The elementary oscillatory kernel attached to a pair of CGL ordinates on
a finite log-ordinate interval. -/
noncomputable def cglCharacterPacketIntervalKernel (A B t u : ℝ) : ℂ :=
  ∫ τ in A..B, cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ)

/-- Exact finite interval form of the character packet's Hermitian mass.
Different characters cancel under the complete residue sum; only the
same-character oscillatory kernels survive. -/
theorem intervalIntegral_cglCharacterPacketHermitianMass_expand (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (A B : ℝ) :
    (∫ τ in A..B, cglCharacterPacketHermitianMass q R w τ) =
      ∑ r, ∑ s,
        (if (w r).character = (w s).character then ((q + 1).totient : ℂ) else 0) *
          cglCharacterPacketIntervalKernel A B (w r).time (w s).time := by
  have hpairCont : ∀ r s : Fin R, Continuous (fun τ : ℝ =>
      cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ)) := by
    intro r s
    exact (continuous_cglCharacterPacketWave (w r).time).mul
      (Complex.continuous_conj.comp (continuous_cglCharacterPacketWave (w s).time))
  have hterm : ∀ r s : Fin R, IntervalIntegrable (fun τ : ℝ =>
      cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ) *
        (if (w r).character = (w s).character then ((q + 1).totient : ℂ) else 0)) volume A B := by
    intro r s
    exact ((hpairCont r s).mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr
    (fun τ _ => cglCharacterPacketHermitianMass_expand q R w τ)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [intervalIntegral.integral_mul_const]
      unfold cglCharacterPacketIntervalKernel
      ring
    · intro s hs
      exact hterm r s
  · intro r hr
    have hsum := IntervalIntegrable.sum Finset.univ (fun s _ => hterm r s)
    have hfun : (∑ s : Fin R, fun τ : ℝ =>
        cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ) *
          (if (w r).character = (w s).character then ((q + 1).totient : ℂ) else 0)) =
        fun τ : ℝ => ∑ s : Fin R,
          cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ) *
            (if (w r).character = (w s).character then ((q + 1).totient : ℂ) else 0) := by
      funext τ
      simp only [Finset.sum_apply]
    rw [hfun] at hsum
    exact hsum

end RHTower
