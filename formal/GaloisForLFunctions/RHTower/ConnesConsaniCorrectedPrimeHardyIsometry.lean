import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence
import GaloisForLFunctions.RHTower.ConnesConsaniPrimeSourceFeatureGram

/-!
# Corrected Hardy realization of the Connes--Consani prime features

Equation (12) of Connes--Consani gives the literal Hardy vectors

`ζ_n(k) = sqrt(8 log p) / (4πn + 3i log p) · x_p(n)^k`,

where `x_p(n) = (4πn-i log p)/(4πn+3i log p)`.  Their exact Gram matrix is the Cauchy kernel
`1/(log p + 2πi(m-n))`.  Combining this with the correctly normalized, total source features from
`ConnesConsaniPrimeSourceFeatureGram` constructs an unconditional isometry from circle `L²` into
Hardy `ℓ²(N)`.  It maps `B_p e_n / sqrt(p-1)` to `ζ_n`, which is the corrected form of Lemma 3.4.
-/

namespace RHTower

open Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

@[simp] theorem starRingEnd_complexMk (a b : ℝ) :
    (starRingEnd ℂ) (Complex.mk a b) = Complex.mk a (-b) := by
  apply Complex.ext <;> simp

theorem complexMk_eq_ofReal_add_I_mul (a b : ℝ) :
    Complex.mk a b = (a : ℂ) + Complex.I * (b : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Cayley node `x_p(n)` in Cartesian coordinates. -/
def connesConsaniPrimeHardyRatio (p : Nat.Primes) (n : ℤ) : ℂ :=
  Complex.mk (4 * Real.pi * (n : ℝ)) (-Real.log (p : ℝ)) /
    Complex.mk (4 * Real.pi * (n : ℝ)) (3 * Real.log (p : ℝ))

theorem connesConsaniPrimeHardyRatio_formula (p : Nat.Primes) (n : ℤ) :
    connesConsaniPrimeHardyRatio p n =
      Complex.mk (4 * Real.pi * (n : ℝ)) (-Real.log (p : ℝ)) /
        Complex.mk (4 * Real.pi * (n : ℝ)) (3 * Real.log (p : ℝ)) := rfl

theorem connesConsaniPrimeHardyDenomPlus_ne_zero (p : Nat.Primes) (n : ℤ) :
    Complex.mk (4 * Real.pi * (n : ℝ)) (3 * Real.log (p : ℝ)) ≠ 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  intro h
  have him := congrArg Complex.im h
  have him0 : 3 * Real.log (p : ℝ) = 0 := by simpa using him
  linarith

theorem connesConsaniPrimeHardyDenomMinus_ne_zero (p : Nat.Primes) (n : ℤ) :
    Complex.mk (4 * Real.pi * (n : ℝ)) (-3 * Real.log (p : ℝ)) ≠ 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  intro h
  have him := congrArg Complex.im h
  have him0 : -3 * Real.log (p : ℝ) = 0 := by simpa using him
  linarith

/-- The paper's Cayley node lies strictly in the unit disk. -/
theorem norm_connesConsaniPrimeHardyRatio_lt_one (p : Nat.Primes) (n : ℤ) :
    ‖connesConsaniPrimeHardyRatio p n‖ < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  let a : ℝ := 4 * Real.pi * (n : ℝ)
  let L : ℝ := Real.log (p : ℝ)
  have hsq : ‖Complex.mk a (-L)‖ ^ (2 : ℕ) < ‖Complex.mk a (3 * L)‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    change a * a + -L * -L < a * a + 3 * L * (3 * L)
    nlinarith
  have hnorm : ‖Complex.mk a (-L)‖ < ‖Complex.mk a (3 * L)‖ := by
    nlinarith [norm_nonneg (Complex.mk a (-L)), norm_nonneg (Complex.mk a (3 * L))]
  rw [connesConsaniPrimeHardyRatio, norm_div, div_lt_one
    (norm_pos_iff.mpr (connesConsaniPrimeHardyDenomPlus_ne_zero p n))]
  exact hnorm

/-- Hardy-kernel node whose coefficient sequence is `x_p(n)^k`. -/
def connesConsaniPrimeHardyNode (p : Nat.Primes) (n : ℤ) : ℂ :=
  starRingEnd ℂ (connesConsaniPrimeHardyRatio p n)

theorem norm_connesConsaniPrimeHardyNode_lt_one (p : Nat.Primes) (n : ℤ) :
    ‖connesConsaniPrimeHardyNode p n‖ < 1 := by
  rw [connesConsaniPrimeHardyNode, Complex.norm_conj]
  exact norm_connesConsaniPrimeHardyRatio_lt_one p n

/-- Literal scalar prefactor in Connes--Consani equation (12). -/
def connesConsaniPrimeHardyScale (p : Nat.Primes) (n : ℤ) : ℂ :=
  ((Real.sqrt (8 * Real.log p) : ℝ) : ℂ) /
    Complex.mk (4 * Real.pi * (n : ℝ)) (3 * Real.log (p : ℝ))

/-- Literal Hardy feature `ζ_n` from Connes--Consani equation (12). -/
def connesConsaniPrimeHardyFeature (p : Nat.Primes) (n : ℤ) : HardyDisk :=
  connesConsaniPrimeHardyScale p n •
    hardyKernel (norm_connesConsaniPrimeHardyNode_lt_one p n)

@[simp] theorem connesConsaniPrimeHardyFeature_apply
    (p : Nat.Primes) (n : ℤ) (k : ℕ) :
    connesConsaniPrimeHardyFeature p n k =
      connesConsaniPrimeHardyScale p n *
        connesConsaniPrimeHardyRatio p n ^ k := by
  rw [connesConsaniPrimeHardyFeature]
  change connesConsaniPrimeHardyScale p n *
    (starRingEnd ℂ (connesConsaniPrimeHardyNode p n)) ^ k = _
  rw [connesConsaniPrimeHardyNode, Complex.conj_conj]

def connesConsaniPrimeHardyCauchyDenom (p : Nat.Primes) (m n : ℤ) : ℂ :=
  Complex.mk (Real.log (p : ℝ)) (2 * Real.pi * ((m - n : ℤ) : ℝ))

theorem connesConsaniPrimeHardyCauchyDenom_eq
    (p : Nat.Primes) (m n : ℤ) :
    (((Real.log p : ℝ) : ℂ) +
      2 * (Real.pi : ℂ) * Complex.I * ((m - n : ℤ) : ℂ)) =
      connesConsaniPrimeHardyCauchyDenom p m n := by
  rw [connesConsaniPrimeHardyCauchyDenom, complexMk_eq_ofReal_add_I_mul]
  push_cast
  ring

theorem connesConsaniPrimeHardyCauchyDenom_ne_zero
    (p : Nat.Primes) (m n : ℤ) :
    connesConsaniPrimeHardyCauchyDenom p m n ≠ 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  intro h
  have hre : Real.log (p : ℝ) = 0 := by
    simpa [connesConsaniPrimeHardyCauchyDenom] using congrArg Complex.re h
  linarith

/-- Exact Cauchy Gram matrix of the literal Hardy features. -/
theorem inner_connesConsaniPrimeHardyFeature (p : Nat.Primes) (m n : ℤ) :
    inner ℂ (connesConsaniPrimeHardyFeature p m)
        (connesConsaniPrimeHardyFeature p n) =
      (1 : ℂ) / connesConsaniPrimeHardyCauchyDenom p m n := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos hp
  let am : ℝ := 4 * Real.pi * (m : ℝ)
  let an : ℝ := 4 * Real.pi * (n : ℝ)
  let L : ℝ := Real.log (p : ℝ)
  let dm : ℂ := Complex.mk am (-3 * L)
  let dn : ℂ := Complex.mk an (3 * L)
  let nm : ℂ := Complex.mk am L
  let nn : ℂ := Complex.mk an (-L)
  let c : ℂ := connesConsaniPrimeHardyCauchyDenom p m n
  let S : ℂ := ((Real.sqrt (8 * L) : ℝ) : ℂ)
  have hsqrtSq : Real.sqrt (8 * Real.log (p : ℝ)) ^ (2 : ℕ) = 8 * Real.log p :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hlogpos.le)
  have hdm : dm ≠ 0 := by
    simpa [dm, am, L] using connesConsaniPrimeHardyDenomMinus_ne_zero p m
  have hdn : dn ≠ 0 := by
    simpa [dn, an, L] using connesConsaniPrimeHardyDenomPlus_ne_zero p n
  have hc : c ≠ 0 := by
    exact connesConsaniPrimeHardyCauchyDenom_ne_zero p m n
  have hL : ((8 * L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) hlogpos.ne')
  have hkey : dn * dm - nn * nm = ((8 * L : ℝ) : ℂ) * c := by
    apply Complex.ext <;>
      simp [dn, dm, nn, nm, c, connesConsaniPrimeHardyCauchyDenom,
        an, am, Complex.mul_re, Complex.mul_im] <;> ring
  have honeEq : 1 - (nn / dn) * (nm / dm) =
      (((8 * L : ℝ) : ℂ) * c) / (dn * dm) := by
    field_simp [hdn, hdm]
    linear_combination hkey
  have hS : S * S = ((8 * L : ℝ) : ℂ) := by
    change ((((Real.sqrt (8 * L) : ℝ) : ℂ) *
      ((Real.sqrt (8 * L) : ℝ) : ℂ))) = ((8 * L : ℝ) : ℂ)
    norm_cast
    simpa [L, pow_two] using hsqrtSq
  rw [connesConsaniPrimeHardyFeature, connesConsaniPrimeHardyFeature,
    inner_smul_left, inner_smul_right,
    inner_hardyKernel_hardyKernel]
  rw [connesConsaniPrimeHardyNode, connesConsaniPrimeHardyNode,
    Complex.conj_conj]
  rw [connesConsaniPrimeHardyScale, connesConsaniPrimeHardyScale,
    connesConsaniPrimeHardyRatio, connesConsaniPrimeHardyRatio,
    connesConsaniPrimeHardyCauchyDenom]
  simp only [map_div₀, Complex.conj_ofReal, starRingEnd_complexMk, neg_neg]
  have hgoal : (S / dm) * (S / dn * (1 - (nn / dn) * (nm / dm))⁻¹) = 1 / c := by
    rw [honeEq, inv_div]
    field_simp [hdm, hdn, hc, hL]
    simpa [pow_two] using hS
  simpa [S, dm, dn, nn, nm, c, L, am, an,
    connesConsaniPrimeHardyCauchyDenom] using hgoal

/-- Correctly normalized literal circle features and paper Hardy features have identical Gram. -/
theorem inner_connesConsaniNormalizedPrimeSourceFeature_eq_hardyFeature
    (p : Nat.Primes) (m n : ℤ) :
    inner ℂ (connesConsaniNormalizedPrimeSourceFeature p m)
        (connesConsaniNormalizedPrimeSourceFeature p n) =
      inner ℂ (connesConsaniPrimeHardyFeature p m)
        (connesConsaniPrimeHardyFeature p n) := by
  rw [inner_connesConsaniNormalizedPrimeSourceFeature,
    inner_connesConsaniPrimeHardyFeature]
  rw [connesConsaniPrimeHardyCauchyDenom_eq]

/-- Corrected source isometry in Connes--Consani Lemma 3.4. -/
def connesConsaniCorrectedPrimeHardyIsometry (p : Nat.Primes) :
    GaussCircleL2 →ₗᵢ[ℂ] HardyDisk :=
  denseSourceFeatureGramIsometry
    (connesConsaniNormalizedPrimeSourceFeature p)
    (connesConsaniPrimeHardyFeature p)
    (inner_connesConsaniNormalizedPrimeSourceFeature_eq_hardyFeature p)
    (dense_connesConsaniNormalizedPrimeSourceFeature p)

/-- The corrected isometry maps each normalized literal source feature to equation `(12)`. -/
theorem connesConsaniCorrectedPrimeHardyIsometry_apply_feature
    (p : Nat.Primes) (n : ℤ) :
    connesConsaniCorrectedPrimeHardyIsometry p
        (connesConsaniNormalizedPrimeSourceFeature p n) =
      connesConsaniPrimeHardyFeature p n := by
  exact denseSourceFeatureGramIsometry_apply
    (connesConsaniNormalizedPrimeSourceFeature p)
    (connesConsaniPrimeHardyFeature p)
    (inner_connesConsaniNormalizedPrimeSourceFeature_eq_hardyFeature p)
    (dense_connesConsaniNormalizedPrimeSourceFeature p) n

end

end RHTower
