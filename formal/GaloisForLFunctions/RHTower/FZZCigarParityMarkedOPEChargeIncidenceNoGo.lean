import GaloisForLFunctions.HTGeometry.FZZCigarReplicaBackreaction
import GaloisForLFunctions.RHTower.FZZCigarParityFixedSupportQuillenReplicaNoGo

/-!
# FZZ marked-OPE charge incidence and same-winding no-go

The remaining FZZ-P producer must derive divisor-mode passivity from the literal torus
replica-area Ward law.  The strongest survivor of the fixed-support Quillen no-go was a mixed
replica-charge/divisor-support term before Jacobian integration.  This file classifies the local
marked OPE part of that survivor.

Halder--Jafferis' fractional-winding operator has winding and radial weights

`w(δ) = 1 - δ`, `r(δ) = 1 - δ / (1 - 2/k)`.

With free-boson normalization fixed by the undeformed FZZ exponents, the exponent inside
`|z|^(2E)` for one marked operator paired with one undeformed operator is

`E_same(δ) = -(k-2) r(δ)/2 + k w(δ)/2 = 1`,
`E_opposite(δ) = -(k-2) r(δ)/2 - k w(δ)/2 = 1-k+kδ`.

Thus the same-winding exponent is exactly replica-independent.  Restoring the `2s'` choices of
marked insertion after the neutral-screening continuation `s'=1/(k-2)` gives zero on the same
charge block and `a(k)δ = 2kδ/(k-2)` on the opposite block.  This resolves the literal `(…)`
left in Halder--Jafferis, arXiv:2402.00932v3, (3.30), as zero and recovers their (3.31) on the
surviving block.

Consequently an arbitrary same-winding prime-form/OPE support kernel has identically zero marked
log-response and cannot select the Abel--Jacobi wall `Im λ = 0`.  This kills the RH chain

`same-winding marked OPE → torus area Ward law → divisor-mode passivity → Mellin completeness → RH`.

The positive survivor is exact: opposite-winding branch cuts remain.  The theorem does not kill
cross-charge OPEs, external BRST vertices, support motion, or higher replica order.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-- Wick exponent inside `|z|^(2E)` for one marked fractional-winding operator paired with one
undeformed operator of the same winding sign. -/
def fzzMarkedSameWindingOPEExponent (k δ : ℝ) : ℝ :=
  -((k - 2) / 2) * replicaRadialWeight (1 / k) δ +
    (k / 2) * replicaWindingWeight δ

/-- Wick exponent inside `|z|^(2E)` for one marked fractional-winding operator paired with one
undeformed operator of the opposite winding sign. -/
def fzzMarkedOppositeWindingOPEExponent (k δ : ℝ) : ℝ :=
  -((k - 2) / 2) * replicaRadialWeight (1 / k) δ -
    (k / 2) * replicaWindingWeight δ

/-- **Exact same-charge cancellation.**  The omitted same-winding coefficient in the marked FZZ
replica integrand is zero: radial and compact variations cancel for every replica deficit. -/
theorem fzzMarkedSameWindingOPEExponent_eq_one
    {k δ : ℝ} (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
    fzzMarkedSameWindingOPEExponent k δ = 1 := by
  rw [fzzMarkedSameWindingOPEExponent, replicaRadialWeight,
    replicaWindingWeight]
  have hden : 1 - 2 * (1 / k) ≠ 0 := by
    intro h
    apply hk2
    field_simp [hk0] at h
    linarith
  field_simp [hk0, hk2, hden]
  ring

/-- The opposite-winding block has base exponent `1-k` and exact marked increment `kδ`. -/
theorem fzzMarkedOppositeWindingOPEExponent_eq
    {k δ : ℝ} (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
    fzzMarkedOppositeWindingOPEExponent k δ = 1 - k + k * δ := by
  rw [fzzMarkedOppositeWindingOPEExponent, replicaRadialWeight,
    replicaWindingWeight]
  have hden : 1 - 2 * (1 / k) ≠ 0 := by
    intro h
    apply hk2
    field_simp [hk0] at h
    linarith
  field_simp [hk0, hk2, hden]
  ring

/-- Symmetry-normalized marked logarithmic OPE response.  The factor `2/(k-2)` restores the
`2s'` choices of marked insertion after the analytic continuation `s'=1/(k-2)`. -/
def fzzMarkedOPELogResponse
    (k δ : ℝ) (sameKernel oppositeKernel : ℂ) : ℂ :=
  (((2 / (k - 2)) *
      (fzzMarkedSameWindingOPEExponent k δ -
        fzzMarkedSameWindingOPEExponent k 0) : ℝ) : ℂ) * sameKernel +
    (((2 / (k - 2)) *
      (fzzMarkedOppositeWindingOPEExponent k δ -
        fzzMarkedOppositeWindingOPEExponent k 0) : ℝ) : ℂ) * oppositeKernel

/-- **Charge-incidence classification.**  First marked replica response is supported only on the
opposite-winding charge block, with the Halder--Jafferis factor `a(k)=2k/(k-2)`. -/
theorem fzzMarkedOPELogResponse_eq_opposite
    {k δ : ℝ} (hk0 : k ≠ 0) (hk2 : k ≠ 2)
    (sameKernel oppositeKernel : ℂ) :
    fzzMarkedOPELogResponse k δ sameKernel oppositeKernel =
      (((2 * k / (k - 2) * δ : ℝ) : ℂ) * oppositeKernel) := by
  rw [fzzMarkedOPELogResponse,
    fzzMarkedSameWindingOPEExponent_eq_one hk0 hk2,
    fzzMarkedSameWindingOPEExponent_eq_one hk0 hk2,
    fzzMarkedOppositeWindingOPEExponent_eq hk0 hk2,
    fzzMarkedOppositeWindingOPEExponent_eq hk0 hk2]
  push_cast
  field_simp [hk2]
  ring

/-- Same-winding marked prime-form/OPE branch with an arbitrary support kernel. -/
def fzzSameWindingMarkedOPELogResponse
    (k δ : ℝ) (kernel : ℂ → ℂ) (d : FZZTorusReplicaAbelData) : ℂ :=
  fzzMarkedOPELogResponse k δ (kernel (fzzTorusAbelJacobiTwist d)) 0

/-- Every same-winding marked support response vanishes, independently of its prime-form kernel
and Abel--Jacobi twist. -/
theorem fzzSameWindingMarkedOPELogResponse_eq_zero
    {k δ : ℝ} (hk0 : k ≠ 0) (hk2 : k ≠ 2)
    (kernel : ℂ → ℂ) (d : FZZTorusReplicaAbelData) :
    fzzSameWindingMarkedOPELogResponse k δ kernel d = 0 := by
  rw [fzzSameWindingMarkedOPELogResponse,
    fzzMarkedOPELogResponse_eq_opposite hk0 hk2]
  ring

/-- **Same-winding marked-OPE route kill.**  No physical level, replica point, support kernel, or
scalar predicate turns this branch into an Abel--Jacobi radial-wall selector. -/
theorem not_exists_physical_fzzSameWindingMarkedOPELogResponse_abelWallSelector :
    ¬ ∃ (k : ℝ), 2 < k ∧ ∃ (δ : ℝ) (kernel : ℂ → ℂ) (P : ℂ → Prop),
      ∀ twist : ℂ,
        P (fzzSameWindingMarkedOPELogResponse k δ kernel
          (fzzCanonicalNeutralAbelData twist 0)) ↔ twist.im = 0 := by
  rintro ⟨k, hk, δ, kernel, P, h⟩
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans (by norm_num) hk)
  have hk2 : k ≠ 2 := ne_of_gt hk
  have hzero := (h 0).mpr (by norm_num)
  rw [fzzSameWindingMarkedOPELogResponse_eq_zero hk0 hk2] at hzero
  have hI : P (fzzSameWindingMarkedOPELogResponse k δ kernel
      (fzzCanonicalNeutralAbelData Complex.I 0)) := by
    rw [fzzSameWindingMarkedOPELogResponse_eq_zero hk0 hk2]
    exact hzero
  have := (h Complex.I).mp hI
  norm_num at this

end

end GaloisForLFunctions.RHTower
