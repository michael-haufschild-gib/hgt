import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBFiniteRankGlobalAIMESourceResponseNoGo
import GaloisForLFunctions.RHTower.SoninOrthonormalCompactVanishing
import GaloisForLFunctions.HTGeometry.LpInjectionCompression
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Compact global AIME source-response no-go

The finite-rank obstruction leaves a serious loophole: an infinite-rank bounded global response
could mix all Xi fibres while remaining compact.  This file closes that entire class on the
literal cubic AIME source in the Hilbert completion `ℓ²(XiZeroCopy)`.

Universal pole cancellation forces the diagonal response coefficient to be exactly `-1` on every
canonical Xi basis vector.  Hence the response norm stays at least one on an infinite orthonormal
sequence.  A compact operator must instead send that sequence to zero.  More sharply, a universally
cancelling response has operator-norm distance at least one from every compact operator.  It is
therefore not compact and, in particular, not Hilbert--Schmidt.

No diagonal, locality, passivity, Schwarz, self-adjointness, finite-band, determinant, or finite-rank
condition is imposed.  The response may mix every Xi fibre and have infinite algebraic rank.  The
source and full response retain the exact cubic real-scale law and half-turn odd phase charge.

The exact intended RH chain is

`source-adapted radiative cancellation` -> `full causal-cut extinction` ->
`source-FE clock covariance` -> the existing FZZ-P/PW-B/RBH Ward transductions -> RH.

`[PROVED HERE] [LEAN-PROVED] [HB ROUTE KILL] [COMPACT-CLASS KILL]`
`[ESSENTIAL-DISTANCE FLOOR] [HILBERT-SCHMIDT CONSEQUENCE]`
`[NOVELTY AUDITED 2026-08-31] [NOVELTY UNVERIFIED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- Hilbert completion of global Xi packets. -/
abbrev D4HBXiHilbertPacket : Type := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Canonical unit vector at one Xi fibre. -/
def d4HBXiHilbertBasisVector (q : XiZeroCopy) : D4HBXiHilbertPacket :=
  lp.single 2 q 1

/-- Canonical Xi basis read along the corpus enumeration of the divisor copies. -/
def d4HBXiHilbertBasisSequence (n : ℕ) : D4HBXiHilbertPacket :=
  d4HBXiHilbertBasisVector (xiOrdinateEquiv n)

/-- The enumerated Xi basis is an infinite orthonormal sequence. -/
theorem d4HBXiHilbertBasisSequence_orthonormal :
    Orthonormal ℂ d4HBXiHilbertBasisSequence := by
  change Orthonormal ℂ
    (lpScalarInjectionBasis (xiOrdinateEquiv : ℕ → XiZeroCopy))
  exact lpScalarInjectionBasis_orthonormal
    (f := (xiOrdinateEquiv : ℕ → XiZeroCopy)) xiOrdinateEquiv.injective

/-- Literal cubic AIME source packet localized at one Xi Hilbert basis vector. -/
def d4HBHilbertAIMESourcePacket (amplitude : ℂ) (q : XiZeroCopy) :
    D4HBXiHilbertPacket :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) •
    d4HBXiHilbertBasisVector q

/-- The Hilbert AIME packet retains the physical half-turn odd charge. -/
theorem d4HBHilbertAIMESourcePacket_neg (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBHilbertAIMESourcePacket (-amplitude) q =
      -d4HBHilbertAIMESourcePacket amplitude q := by
  unfold d4HBHilbertAIMESourcePacket
  rw [d4FundamentalQNMCrossBranchAIMENumerator_neg]
  simp

/-- The Hilbert AIME packet is cubic under real seed rescaling. -/
theorem d4HBHilbertAIMESourcePacket_realScale
    (scale : ℝ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBHilbertAIMESourcePacket ((scale : ℂ) * amplitude) q =
      ((scale ^ 3 : ℝ) : ℂ) • d4HBHilbertAIMESourcePacket amplitude q := by
  unfold d4HBHilbertAIMESourcePacket
  rw [d4FundamentalQNMCrossBranchAIMENumerator_realScale]
  simp [smul_smul]

/-- Full pole coefficient after an arbitrary bounded complex-linear global Hilbert response acts on
the literal cubic AIME source. -/
def d4HBCompactAIMESourceResponseFullPoleNumerator
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
    Delta (d4HBHilbertAIMESourcePacket amplitude q) q

/-- Every bounded complex-linear response to the literal source preserves half-turn oddness. -/
theorem d4HBCompactAIMESourceResponseFullPoleNumerator_neg
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBCompactAIMESourceResponseFullPoleNumerator Delta (-amplitude) q =
      -d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q := by
  unfold d4HBCompactAIMESourceResponseFullPoleNumerator
  rw [d4FundamentalQNMCrossBranchAIMENumerator_neg,
    d4HBHilbertAIMESourcePacket_neg, map_neg]
  simp
  ring

/-- Every bounded complex-linear response to the literal source preserves cubic real homogeneity. -/
theorem d4HBCompactAIMESourceResponseFullPoleNumerator_realScale
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (scale : ℝ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBCompactAIMESourceResponseFullPoleNumerator Delta
        ((scale : ℂ) * amplitude) q =
      ((scale ^ 3 : ℝ) : ℂ) *
        d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q := by
  unfold d4HBCompactAIMESourceResponseFullPoleNumerator
  rw [d4FundamentalQNMCrossBranchAIMENumerator_realScale,
    d4HBHilbertAIMESourcePacket_realScale, map_smul]
  simp [smul_eq_mul]
  ring

/-- Universal cancellation forces exact diagonal coefficient `-1` on every Xi basis vector. -/
theorem d4HBCompactAIMESourceResponse_diagonal_eq_neg_one
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (hcancel : ∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0)
    (q : XiZeroCopy) :
    Delta (d4HBXiHilbertBasisVector q) q = -1 := by
  let N := d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)
  have hN : N ≠ 0 := by
    exact (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha
  have h := hcancel q
  change N + Delta (N • d4HBXiHilbertBasisVector q) q = 0 at h
  rw [map_smul] at h
  change N + N * Delta (d4HBXiHilbertBasisVector q) q = 0 at h
  have hfactor : N * (1 + Delta (d4HBXiHilbertBasisVector q) q) = 0 := by
    simpa [mul_add] using h
  have hadd : 1 + Delta (d4HBXiHilbertBasisVector q) q = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hN
  exact eq_neg_of_add_eq_zero_right hadd

/-- Exact diagonal coefficient `-1` gives a dimension-free norm floor on every Xi basis image. -/
theorem d4HBCompactAIMESourceResponse_one_le_norm_basis
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (hcancel : ∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0)
    (q : XiZeroCopy) :
    1 ≤ ‖Delta (d4HBXiHilbertBasisVector q)‖ := by
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (Delta (d4HBXiHilbertBasisVector q)) q
  rw [d4HBCompactAIMESourceResponse_diagonal_eq_neg_one Delta amplitude ha hcancel q,
    norm_neg, norm_one] at hcoord
  exact hcoord

/-- No compact bounded global response can cancel cubic AIME on every Xi fibre, even with arbitrary
cross-fibre mixing and infinite algebraic rank. -/
theorem not_d4HBCompactAIMESourceResponse_universalCancellation
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (hcancel : ∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) :
    ¬ IsCompactOperator Delta := by
  let v : ℕ → D4HBXiHilbertPacket := d4HBXiHilbertBasisSequence
  have hv : Orthonormal ℂ v := d4HBXiHilbertBasisSequence_orthonormal
  apply not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge Delta v 1 1
  · intro n
    exact le_of_eq (hv.1 n)
  · intro ell
    exact tendsto_apply_orthonormal_atTop_zero hv ell
  · exact zero_lt_one
  · intro n
    exact d4HBCompactAIMESourceResponse_one_le_norm_basis
      Delta amplitude ha hcancel (xiOrdinateEquiv n)

/-- Sharp positive survivor: a universally cancelling response lies at operator-norm distance at
least one from every compact operator. -/
theorem d4HBCompactAIMESourceResponse_one_le_norm_sub_compact
    (Delta K : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (hcancel : ∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0)
    (hK : IsCompactOperator K) :
    1 ≤ ‖Delta - K‖ := by
  by_contra hnorm
  have hlt : ‖Delta - K‖ < 1 := lt_of_not_ge hnorm
  have hgap : 0 < 1 - ‖Delta - K‖ := sub_pos.mpr hlt
  let v : ℕ → D4HBXiHilbertPacket := d4HBXiHilbertBasisSequence
  have hv : Orthonormal ℂ v := d4HBXiHilbertBasisSequence_orthonormal
  have hcompactZero : Tendsto (fun n => ‖K (v n)‖) atTop (𝓝 0) :=
    tendsto_norm_compactOperator_apply_orthonormal hK hv
  have hsmall : ∀ᶠ n in atTop, ‖K (v n)‖ < 1 - ‖Delta - K‖ :=
    (tendsto_order.mp hcompactZero).2 _ hgap
  obtain ⟨n, hn⟩ := hsmall.exists
  have hvnorm : ‖v n‖ = 1 := hv.1 n
  have hDeltaLower : 1 ≤ ‖Delta (v n)‖ := by
    exact d4HBCompactAIMESourceResponse_one_le_norm_basis
      Delta amplitude ha hcancel (xiOrdinateEquiv n)
  have htriangle :
      ‖Delta (v n)‖ ≤ ‖(Delta - K) (v n)‖ + ‖K (v n)‖ := by
    have heq : Delta (v n) = (Delta - K) (v n) + K (v n) := by
      simp
    rw [heq]
    exact norm_add_le _ _
  have hop : ‖(Delta - K) (v n)‖ ≤ ‖Delta - K‖ := by
    calc
      ‖(Delta - K) (v n)‖ ≤ ‖Delta - K‖ * ‖v n‖ :=
        (Delta - K).le_opNorm (v n)
      _ = ‖Delta - K‖ := by rw [hvnorm, mul_one]
  have hone : (1 : ℝ) < 1 := calc
    1 ≤ ‖Delta (v n)‖ := hDeltaLower
    _ ≤ ‖(Delta - K) (v n)‖ + ‖K (v n)‖ := htriangle
    _ ≤ ‖Delta - K‖ + ‖K (v n)‖ := by nlinarith
    _ < ‖Delta - K‖ + (1 - ‖Delta - K‖) := by nlinarith
    _ = 1 := by ring
  exact (lt_irrefl (1 : ℝ)) hone

/-- Hilbert--Schmidt consequence of the compact-class obstruction. -/
theorem not_d4HBHilbertSchmidtAIMESourceResponse_universalCancellation
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (hcancel : ∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) :
    ¬ Delta.IsHilbertSchmidt := by
  intro hHS
  exact not_d4HBCompactAIMESourceResponse_universalCancellation
    Delta amplitude ha hcancel hHS.isCompactOperator

/-- Closed route class: no compact bounded complex-linear global response to the literal cubic,
phase-odd AIME source supplies universal HB pole cancellation. -/
def D4HBCompactGlobalAIMESourceResponseCancellationRouteKilled : Prop :=
  ∀ (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket),
    IsCompactOperator Delta →
    ∀ amplitude : ℂ, amplitude ≠ 0 →
      ¬ (∀ q : XiZeroCopy,
        d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0)

/-- Premise-free certificate killing the compact global source-adapted HB response class. -/
theorem d4HBCompactGlobalAIMESourceResponseCancellationRouteKilled :
    D4HBCompactGlobalAIMESourceResponseCancellationRouteKilled := by
  intro Delta hcompact amplitude ha hcancel
  exact not_d4HBCompactAIMESourceResponse_universalCancellation
    Delta amplitude ha hcancel hcompact

end

end RHTower
