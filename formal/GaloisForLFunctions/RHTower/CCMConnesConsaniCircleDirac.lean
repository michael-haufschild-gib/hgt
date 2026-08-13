import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse
import GaloisForLFunctions.HTGeometry.FiniteSmoothCompression
import GaloisForLFunctions.RHTower.DeningerPhaseGenerator

/-!
# The Connes--Consani circle Dirac operator

For a circle of length `L > 0`, the Fourier-side Dirac operator is the maximal real diagonal
operator with eigenvalues `2πn/L`, `n ∈ ℤ`.  This file constructs its explicit bounded resolvent
at `i`, proves both inverse laws on the maximal domain, and proves compactness from escape of the
integer spectrum through the cofinite filter.

This is the unperturbed compact-resolvent input to Connes--Consani's `propDpert`.  No spectral
assumption or abstract compact-resolvent premise is used.
-/

open Module Topology Filter

namespace RHTower

open HilbertSchmidt GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive circle lengths, so source-level statements carry no positivity premise. -/
abbrev CCMCircleLength := {L : ℝ // 0 < L}

/-- Fourier frequency `2πn/L` on the circle of length `L`. -/
def ccmCircleFrequency (L : ℝ) (n : ℤ) : ℝ :=
  2 * Real.pi * (n : ℝ) / L

/-- The maximal-domain circle Dirac operator in the Fourier basis. -/
def ccmCircleDirac (L : ℝ) : DiagonalL2 ℤ →ₗ.[ℂ] DiagonalL2 ℤ :=
  deningerPhaseGenerator (ccmCircleFrequency L)

/-- The circle Dirac operator is self-adjoint on its maximal domain. -/
theorem ccmCircleDirac_isSelfAdjoint (L : ℝ) :
    IsSelfAdjoint (ccmCircleDirac L) :=
  deningerPhaseGenerator_isSelfAdjoint (ccmCircleFrequency L)

/-- Diagonal multiplier of the resolvent `(D₀-i)⁻¹`. -/
def ccmCircleResolventMultiplier (L : ℝ) (n : ℤ) : ℂ :=
  ((ccmCircleFrequency L n : ℂ) - Complex.I)⁻¹

theorem ccmCircleResolventMultiplier_norm_le_one (L : ℝ) (n : ℤ) :
    ‖ccmCircleResolventMultiplier L n‖ ≤ 1 := by
  rw [ccmCircleResolventMultiplier, norm_inv]
  have him : (((ccmCircleFrequency L n : ℂ) - Complex.I)).im = -1 := by simp
  have hden : 1 ≤ ‖(ccmCircleFrequency L n : ℂ) - Complex.I‖ := by
    have h := Complex.abs_im_le_norm ((ccmCircleFrequency L n : ℂ) - Complex.I)
    rw [him, abs_neg, abs_one] at h
    exact h
  exact (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden

/-- Explicit bounded resolvent of the circle Dirac operator at `i`. -/
def ccmCircleResolvent (L : ℝ) : DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ :=
  lpDiagonalCLM (ccmCircleResolventMultiplier L) zero_le_one
    (ccmCircleResolventMultiplier_norm_le_one L)

theorem ccmCircleFrequency_abs_tendsto_cofinite (hL : 0 < L) :
    Tendsto (fun n : ℤ => |ccmCircleFrequency L n|) cofinite atTop := by
  have habsZ : Tendsto (fun n : ℤ => |n|) cofinite atTop := by
    rw [Int.cofinite_eq]
    exact tendsto_sup.mpr ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
  have habsR : Tendsto (fun n : ℤ => |(n : ℝ)|) cofinite atTop := by
    refine (tendsto_intCast_atTop_atTop.comp habsZ).congr fun n => ?_
    simp
  have hscale : 0 < 2 * Real.pi / L := by positivity
  refine (Tendsto.const_mul_atTop hscale habsR).congr fun n => ?_
  rw [ccmCircleFrequency, abs_div, abs_mul, abs_of_pos hL,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  ring

/-- The explicit circle resolvent is compact. -/
theorem ccmCircleResolvent_compact (hL : 0 < L) :
    IsCompactOperator (ccmCircleResolvent L) := by
  apply isCompactOperator_resolvent_of_tendsto_cofinite (lpBasis ℤ)
    (lam := ccmCircleFrequency L)
  · intro n
    rw [lpBasis_apply]
    calc
      ccmCircleResolvent L (lp.single 2 n (1 : ℂ)) =
          lp.single 2 n (ccmCircleResolventMultiplier L n) :=
        lpDiagonalCLM_single (ccmCircleResolventMultiplier L) zero_le_one
          (ccmCircleResolventMultiplier_norm_le_one L) n
      _ = ccmCircleResolventMultiplier L n • lp.single 2 n (1 : ℂ) := by
        rw [← lp.single_smul]
        simp
      _ = ((ccmCircleFrequency L n : ℂ) - Complex.I)⁻¹ •
          lp.single 2 n (1 : ℂ) := by rw [ccmCircleResolventMultiplier]
  · exact ccmCircleFrequency_abs_tendsto_cofinite hL

/-- The explicit resolvent maps all of `ℓ²(ℤ)` into the maximal Dirac domain. -/
theorem ccmCircleResolvent_mem_domain (L : ℝ) (x : DiagonalL2 ℤ) :
    ccmCircleResolvent L x ∈ (ccmCircleDirac L).domain := by
  let mu : ℤ → ℂ := fun n =>
    (ccmCircleFrequency L n : ℂ) * ccmCircleResolventMultiplier L n
  have hmu : ∀ n, ‖mu n‖ ≤ 1 := by
    intro n
    simp only [mu, norm_mul, ccmCircleResolventMultiplier, norm_inv]
    have hre : |ccmCircleFrequency L n| ≤
        ‖(ccmCircleFrequency L n : ℂ) - Complex.I‖ := by
      have h := Complex.abs_re_le_norm ((ccmCircleFrequency L n : ℂ) - Complex.I)
      simpa using h
    have hdenpos : 0 < ‖(ccmCircleFrequency L n : ℂ) - Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((ccmCircleFrequency L n : ℂ) - Complex.I)
      have hden : 1 ≤ ‖(ccmCircleFrequency L n : ℂ) - Complex.I‖ := by simpa using h
      exact zero_lt_one.trans_le hden
    rw [mul_inv_le_iff₀ hdenpos]
    simpa using hre
  let y : DiagonalL2 ℤ := lpDiagonalCLM mu zero_le_one hmu x
  change Memℓp (fun n => (ccmCircleFrequency L n : ℂ) * (ccmCircleResolvent L x) n) 2
  rw [show (fun n => (ccmCircleFrequency L n : ℂ) * (ccmCircleResolvent L x) n) =
      fun n => y n by
    funext n
    simp only [y, mu, ccmCircleResolvent, lpDiagonalCLM_apply]
    ring]
  exact lp.memℓp y

/-- **Exact compact resolvent for the Connes--Consani circle Dirac operator.** -/
theorem ccmCircleDirac_hasCompactResolventAt_I (hL : 0 < L) :
    LinearPMap.HasCompactResolventAt (ccmCircleDirac L) Complex.I := by
  refine ⟨ccmCircleResolvent L, ccmCircleResolvent_compact hL,
    ⟨ccmCircleResolvent_mem_domain L, ?_⟩, ?_⟩
  · intro x
    apply lp.ext
    funext n
    change
      (ccmCircleFrequency L n : ℂ) * (ccmCircleResolvent L x) n -
        Complex.I * (ccmCircleResolvent L x) n = x n
    simp only [ccmCircleResolvent, lpDiagonalCLM_apply]
    rw [← sub_mul]
    have hne : (ccmCircleFrequency L n : ℂ) - Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    rw [ccmCircleResolventMultiplier, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · intro x
    apply lp.ext
    funext n
    change (ccmCircleResolventMultiplier L n) *
      ((ccmCircleFrequency L n : ℂ) * (x : DiagonalL2 ℤ) n -
        Complex.I * (x : DiagonalL2 ℤ) n) = (x : DiagonalL2 ℤ) n
    rw [← sub_mul]
    have hne : (ccmCircleFrequency L n : ℂ) - Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    rw [ccmCircleResolventMultiplier, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ## Exact Connes--Consani finite smooth compression -/

/-- A Connes--Consani packet is finite data already living in the maximal circle Dirac domain. -/
abbrev CCMCircleSmoothPacket (L : CCMCircleLength) (k : ℕ) :=
  Fin k → (ccmCircleDirac (L : ℝ)).domain

/-- Orthogonal projection onto a finite Connes--Consani smooth packet. -/
def ccmConnesConsaniProjection (L : CCMCircleLength) {k : ℕ}
    (v : CCMCircleSmoothPacket L k) : DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ :=
  smoothPacketProjection (ccmCircleDirac (L : ℝ)) v

/-- The exact source compression `(1-Π)D₀(1-Π)` on the maximal Dirac domain. -/
def ccmConnesConsaniCompressedDirac (L : CCMCircleLength) {k : ℕ}
    (v : CCMCircleSmoothPacket L k) : DiagonalL2 ℤ →ₗ.[ℂ] DiagonalL2 ℤ :=
  smoothPacketCompressedOperator (ccmCircleDirac (L : ℝ)) v

/-- The constructed operator is literally the source formula `(1-Π)D₀(1-Π)`. -/
theorem ccmConnesConsaniCompressedDirac_apply (L : CCMCircleLength) {k : ℕ}
    (v : CCMCircleSmoothPacket L k)
    (x : (ccmConnesConsaniCompressedDirac L v).domain) :
    ccmConnesConsaniCompressedDirac L v x =
      (1 - ccmConnesConsaniProjection L v)
        (ccmCircleDirac (L : ℝ)
          ⟨(1 - ccmConnesConsaniProjection L v) (x : DiagonalL2 ℤ), by
            have hx : (x : DiagonalL2 ℤ) ∈ (ccmCircleDirac (L : ℝ)).domain := x.property
            exact (ccmCircleDirac (L : ℝ)).domain.sub_mem hx
              (smoothPacketProjection_mem_domain (ccmCircleDirac (L : ℝ)) v x)⟩) :=
  smoothPacketCompressedOperator_apply (ccmCircleDirac (L : ℝ))
    (ccmCircleDirac_isSelfAdjoint (L : ℝ)) v x

/-- **Connes--Consani `propDpert`, self-adjointness clause.**

Every finite smooth packet compression of the circle Dirac operator is self-adjoint on exactly the
original maximal domain.  Smoothness is intrinsic to `CCMCircleSmoothPacket`; this theorem has no
analytic premise. -/
theorem connesConsani_propDpert_isSelfAdjoint (L : CCMCircleLength) {k : ℕ}
    (v : CCMCircleSmoothPacket L k) :
    IsSelfAdjoint (ccmConnesConsaniCompressedDirac L v) :=
  smoothPacketCompressedOperator_isSelfAdjoint (ccmCircleDirac (L : ℝ))
    (ccmCircleDirac_isSelfAdjoint (L : ℝ)) v

/-- **Connes--Consani `propDpert`, compact-resolvent clause.**

Every finite smooth packet compression has a compact two-sided resolvent at `i`.  Unlike the paper's
one-line Kato--Rellich argument, this includes the missing compact-resolvent proof. -/
theorem connesConsani_propDpert_hasCompactResolventAt_I (L : CCMCircleLength) {k : ℕ}
    (v : CCMCircleSmoothPacket L k) :
    LinearPMap.HasCompactResolventAt (ccmConnesConsaniCompressedDirac L v) Complex.I :=
  smoothPacketCompressedOperator_hasCompactResolventAt_I (ccmCircleDirac (L : ℝ))
    (ccmCircleDirac_isSelfAdjoint (L : ℝ))
    (ccmCircleDirac_hasCompactResolventAt_I L.property) v

end

end RHTower
