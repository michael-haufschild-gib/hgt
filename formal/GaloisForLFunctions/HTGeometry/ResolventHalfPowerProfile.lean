import GaloisForLFunctions.HTGeometry.InverseSqrtBinomialSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The half-power resolvent profile and its derivatives

Writing the terminal resolvent as its binomial series with the scale factored out,

`(L − T/2)^{-a} = Σ_k binom(2k,k) 4^{-k} 2^{-k} L^{-(k+a)} T^k`,

differentiating in `L` is termwise and only shifts the exponent: each term acquires the factor
`−(k+a)` and the exponent `−(k+a+1)`.  No new series is needed to differentiate — the whole tower of
derivatives lives in the same family, and the classical coefficients appear on their own:

`a = 1/2` gives `−(k+1/2) = −(2k+1)/2`,  `a = 3/2` gives `(k+1/2)(k+3/2) = (2k+1)(2k+3)/4`,

which are exactly the coefficients of `(1−s)^{-3/2}` and `(1−s)^{-5/2}`.  Termwise differentiation
is legitimate on any terminal ray `L > L₀` with `‖T‖ < 2L₀`, where the derivative terms are
dominated by `(k+a) L₀^{-a-1} (‖T‖/2L₀)^k`.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-! ## The scalar weights -/

/-- The scalar weight of the `k`-th term of the half-power resolvent profile. -/
def resolventCoeff (a : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * L ^ (-((k : ℝ) + a))

/-- The termwise derivative weight. -/
def resolventCoeffDeriv (a : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * (-((k : ℝ) + a)) * L ^ (-((k : ℝ) + a) - 1)

theorem hasDerivAt_resolventCoeff (a : ℝ) (k : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (resolventCoeff a k) (resolventCoeffDeriv a k L) L := by
  have hbase : HasDerivAt (fun x : ℝ => x ^ (-((k : ℝ) + a)))
      ((-((k : ℝ) + a)) * L ^ (-((k : ℝ) + a) - 1)) L :=
    Real.hasDerivAt_rpow_const (Or.inl hL)
  have hmul := hbase.const_mul (normalizedCentralBinom k * (1 / 2 : ℝ) ^ k)
  have heq : normalizedCentralBinom k * (1 / 2 : ℝ) ^ k *
      ((-((k : ℝ) + a)) * L ^ (-((k : ℝ) + a) - 1)) = resolventCoeffDeriv a k L := by
    rw [resolventCoeffDeriv]
    ring
  rw [← heq]
  exact hmul

theorem rpow_neg_natCast {L : ℝ} (hL : 0 < L) (k : ℕ) : L ^ (-(k : ℝ)) = (L⁻¹) ^ k := by
  rw [Real.rpow_neg hL.le, Real.rpow_natCast, ← inv_pow]

/-! ## The uniform termwise bound on a terminal ray -/

theorem norm_resolventDerivTerm_le {T : A} {a L₀ L : ℝ} (ha : 0 ≤ a) (hL₀ : 0 < L₀)
    (hL : L₀ < L) (k : ℕ) :
    ‖resolventCoeffDeriv a k L • T ^ k‖
      ≤ (((k : ℝ) + a) * L₀ ^ (-a - 1)) * (‖T‖ / (2 * L₀)) ^ k := by
  have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
  have hka : (0 : ℝ) ≤ (k : ℝ) + a := by positivity
  have hcnn : 0 ≤ normalizedCentralBinom k := normalizedCentralBinom_nonneg k
  have hcle : normalizedCentralBinom k ≤ 1 := normalizedCentralBinom_le_one k
  have hsplit : L ^ (-((k : ℝ) + a) - 1) = L ^ (-(k : ℝ)) * L ^ (-a - 1) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  have hmono1 : L ^ (-(k : ℝ)) ≤ L₀ ^ (-(k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hL₀ hL.le (neg_nonpos.mpr (Nat.cast_nonneg k))
  have hmono2 : L ^ (-a - 1) ≤ L₀ ^ (-a - 1) :=
    Real.rpow_le_rpow_of_nonpos hL₀ hL.le (by linarith)
  have habs : |resolventCoeffDeriv a k L|
      = normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * ((k : ℝ) + a)
        * (L ^ (-(k : ℝ)) * L ^ (-a - 1)) := by
    rw [resolventCoeffDeriv, hsplit, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hcnn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ L ^ (-(k : ℝ)) * L ^ (-a - 1)),
      abs_of_nonpos (by linarith : (-((k : ℝ) + a)) ≤ 0)]
    ring
  have hcoeff : |resolventCoeffDeriv a k L|
      ≤ ((k : ℝ) + a) * L₀ ^ (-a - 1) * ((1 / 2 : ℝ) ^ k * L₀ ^ (-(k : ℝ))) := by
    rw [habs]
    have hprod : L ^ (-(k : ℝ)) * L ^ (-a - 1) ≤ L₀ ^ (-(k : ℝ)) * L₀ ^ (-a - 1) :=
      mul_le_mul hmono1 hmono2 (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hL₀.le _)
    calc normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * ((k : ℝ) + a)
          * (L ^ (-(k : ℝ)) * L ^ (-a - 1))
        ≤ 1 * (1 / 2 : ℝ) ^ k * ((k : ℝ) + a) * (L₀ ^ (-(k : ℝ)) * L₀ ^ (-a - 1)) := by
          refine mul_le_mul ?_ hprod (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcle (by positivity)) hka
      _ = ((k : ℝ) + a) * L₀ ^ (-a - 1) * ((1 / 2 : ℝ) ^ k * L₀ ^ (-(k : ℝ))) := by ring
  have hgeom : (1 / 2 : ℝ) ^ k * L₀ ^ (-(k : ℝ)) * ‖T‖ ^ k = (‖T‖ / (2 * L₀)) ^ k := by
    rw [rpow_neg_natCast hL₀ k, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  calc ‖resolventCoeffDeriv a k L • T ^ k‖
      = |resolventCoeffDeriv a k L| * ‖T ^ k‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (((k : ℝ) + a) * L₀ ^ (-a - 1) * ((1 / 2 : ℝ) ^ k * L₀ ^ (-(k : ℝ)))) * ‖T‖ ^ k := by
        refine mul_le_mul hcoeff (norm_pow_le T k) (norm_nonneg _) (by positivity)
    _ = (((k : ℝ) + a) * L₀ ^ (-a - 1)) * (‖T‖ / (2 * L₀)) ^ k := by
        rw [← hgeom]
        ring

omit [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem summable_resolventDerivMajorant {T : A} {a L₀ : ℝ} (hL₀ : 0 < L₀)
    (hT : ‖T‖ < 2 * L₀) :
    Summable fun k : ℕ => (((k : ℝ) + a) * L₀ ^ (-a - 1)) * (‖T‖ / (2 * L₀)) ^ k := by
  set ρ : ℝ := ‖T‖ / (2 * L₀) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one (by positivity)]
    exact hT
  have hnorm : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0]
  have hk : Summable fun k : ℕ => (k : ℝ) * ρ ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm |>.congr fun k => by rw [pow_one]
  have hgeo : Summable fun k : ℕ => ρ ^ k := summable_geometric_of_lt_one hρ0 hρ1
  have hsum : Summable fun k : ℕ => ((k : ℝ) * ρ ^ k + a * ρ ^ k) := hk.add (hgeo.mul_left a)
  refine (hsum.mul_right (L₀ ^ (-a - 1))).congr fun k => ?_
  ring

/-! ## The profile and its derivative -/

/-- The half-power resolvent profile. -/
def resolventProfile (T : A) (a L : ℝ) : A := ∑' k : ℕ, resolventCoeff a k L • T ^ k

/-- The termwise derivative of the profile. -/
def resolventProfileDeriv (T : A) (a L : ℝ) : A := ∑' k : ℕ, resolventCoeffDeriv a k L • T ^ k

/-- **The profile is differentiable termwise on a terminal ray.**  Its derivative is the same
series with the exponent shifted and the factor `−(k+a)` inserted. -/
theorem hasDerivAt_resolventProfile {T : A} {a L₀ L : ℝ} (ha : 0 ≤ a) (hL₀ : 0 < L₀)
    (hT : ‖T‖ < 2 * L₀) (hL : L ∈ Ioi L₀)
    (hsum : Summable fun k : ℕ => resolventCoeff a k (L₀ + 1) • T ^ k) :
    HasDerivAt (resolventProfile T a) (resolventProfileDeriv T a L) L := by
  have hopen : IsOpen (Ioi L₀) := isOpen_Ioi
  have hconn : IsPreconnected (Ioi L₀) := (convex_Ioi L₀).isPreconnected
  have hmem : (L₀ + 1) ∈ Ioi L₀ := by
    simp only [mem_Ioi]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected
    (summable_resolventDerivMajorant (T := T) (a := a) hL₀ hT) hopen hconn
    (fun k y hy => ((hasDerivAt_resolventCoeff a k
      (ne_of_gt (lt_trans hL₀ hy))).smul_const (T ^ k)))
    (fun k y hy => norm_resolventDerivTerm_le ha hL₀ hy k) hmem hsum hL

end GaloisForLFunctions.HTGeometry
