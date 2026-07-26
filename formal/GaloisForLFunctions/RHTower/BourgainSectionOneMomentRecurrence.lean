/-
# Exact moment algebra for Bourgain (1.19)--(1.26)

For `d = 4`, the local decoupling contribution is

`b(K)^12 K^2 Q`.

The quadratic planar refinement contributes

`C^12 N^(12δ) (N/K)^2 S`.

The `K` powers cancel exactly, leaving

`(C b(K) N^δ)^12 N^2 S`.

This module records that cancellation before the analytic cube and
wave-packet estimates are assembled.
-/
import GaloisForLFunctions.RHTower.BourgainSectionOneScaleSelection

namespace RHTower

noncomputable section

/-- Twelfth-moment form of Bourgain's bilinear decoupling bound in
dimension four. -/
def BourgainSectionOneMomentBound
    (N b L S : ℝ) : Prop :=
  L ≤ b ^ (12 : ℕ) * N ^ (2 : ℕ) * S

/-- Exact algebraic passage from (1.19), through (1.25), to (1.26). -/
theorem bourgainSectionOneMomentRecurrence
    {N K C bK L Q S δ : ℝ}
    (hN : 0 < N) (hK : 0 < K)
    (hlocal :
      L ≤ bK ^ (12 : ℕ) * K ^ (2 : ℕ) * Q)
    (hplanar :
      Q ≤ C ^ (12 : ℕ) * N ^ (12 * δ) *
        (N / K) ^ (2 : ℕ) * S) :
    BourgainSectionOneMomentBound
      N (C * bK * N ^ δ) L S := by
  have hpref :
      0 ≤ bK ^ (12 : ℕ) * K ^ (2 : ℕ) := by
    positivity
  have hcombined :
      L ≤
        bK ^ (12 : ℕ) * K ^ (2 : ℕ) *
          (C ^ (12 : ℕ) * N ^ (12 * δ) *
            (N / K) ^ (2 : ℕ) * S) :=
    hlocal.trans (mul_le_mul_of_nonneg_left hplanar hpref)
  unfold BourgainSectionOneMomentBound
  calc
    L ≤
        bK ^ (12 : ℕ) * K ^ (2 : ℕ) *
          (C ^ (12 : ℕ) * N ^ (12 * δ) *
            (N / K) ^ (2 : ℕ) * S) := hcombined
    _ = (C * bK * N ^ δ) ^ (12 : ℕ) *
        N ^ (2 : ℕ) * S := by
      have hNpow :
          (N ^ δ) ^ (12 : ℕ) = N ^ (12 * δ) := by
        rw [← Real.rpow_mul_natCast hN.le]
        congr 1
        ring
      rw [mul_pow, mul_pow, hNpow]
      field_simp

/-- Root-form consequence: the scale-`N` decoupling coefficient may be
chosen as `C * bK * N^δ`. -/
theorem bourgainSectionOneCoefficientRecurrence
    {N K C bK bN L Q S δ : ℝ}
    (hN : 0 < N) (hK : 0 < K)
    (hC : 0 ≤ C) (hbK : 0 ≤ bK) (hS : 0 ≤ S)
    (hlocal :
      L ≤ bK ^ (12 : ℕ) * K ^ (2 : ℕ) * Q)
    (hplanar :
      Q ≤ C ^ (12 : ℕ) * N ^ (12 * δ) *
        (N / K) ^ (2 : ℕ) * S)
    (hbN :
      C * bK * N ^ δ ≤ bN) :
    BourgainSectionOneMomentBound N bN L S := by
  have hbase :=
    bourgainSectionOneMomentRecurrence
      hN hK hlocal hplanar
  have hcoeff0 : 0 ≤ C * bK * N ^ δ := by
    positivity
  have hpow :
      (C * bK * N ^ δ) ^ (12 : ℕ) ≤
        bN ^ (12 : ℕ) :=
    pow_le_pow_left₀ hcoeff0 hbN 12
  unfold BourgainSectionOneMomentBound at hbase ⊢
  exact hbase.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (sq_nonneg N))
      hS)

end

end RHTower
