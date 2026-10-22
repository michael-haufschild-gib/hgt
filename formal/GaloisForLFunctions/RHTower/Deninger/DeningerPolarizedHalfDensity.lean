import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPolarizedTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The half-density normalization of a polarized power transfer

Coefficient spaces indexed by a modulus carry Poincaré pairings `B_r` and odd Hodge operators
`J_r`, and a degree `n` power correspondence supplies a pullback `V_n : H_r → H_{nr}` and a
pushforward `F_n : H_{nr} → H_r`.  Under projection-formula adjunction, Hodge naturality, and the
degree law `F_n V_n = n`, the cup--Hodge metric `g_r(x,y) = B_r(x, J_r y)` scales by the degree.

Consequently the half-density normalization `U_n = n^{-1/2} V_n` is an isometry, it is
multiplicative wherever the pullbacks are, and the unnormalized transfer factors as
`V_n = e^{t/2} U_n` at discrete time `t = log n`.  That factorization is the source of the
weight-one half shift, obtained from degree and adjunction alone.

* `DeningerPolarizedTransfer` : the data and its three axioms.
* `DeningerPolarizedTransfer.metric_pull` : `g_{nr}(V_n x, V_n y) = n g_r(x,y)`.
* `DeningerPolarizedTransfer.metric_normalized` : `U_n` is an isometry.
* `DeningerPolarizedTransfer.normalized_comp` : `U_m U_n = U_{mn}`.
* `DeningerPolarizedTransfer.pull_eq_expHalfLog_smul_normalized` : `V_n = e^{(log n)/2} U_n`.
-/

namespace RHTower

section HalfDensity

variable {ι : Type*} {H : ι → Type*}

section Transport

variable (H)

/-- Transport of a coefficient along an equality of moduli. -/
def deningerModulusCast {a b : ι} (h : a = b) (z : H a) : H b :=
  cast (congrArg H h) z

variable {H}

theorem deningerModulusCast_smul [∀ r, AddCommGroup (H r)] [∀ r, Module ℝ (H r)]
    {a b : ι} (h : a = b) (c : ℝ) (z : H a) :
    deningerModulusCast H h (c • z) = c • deningerModulusCast H h z := by
  subst h
  rfl

end Transport

theorem deningerSqrtNatCast_ne_zero {n : ℕ} (hn : 0 < n) : Real.sqrt n ≠ 0 :=
  (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'

variable [∀ r, AddCommGroup (H r)] [∀ r, Module ℝ (H r)]

/-- Polarized transfer data: coefficient spaces indexed by a modulus, a pullback and a
pushforward for each degree, Poincaré pairings, and odd Hodge operators, subject to
projection-formula adjunction, Hodge naturality, and the push--pull degree law. -/
structure DeningerPolarizedTransfer (ι : Type*) (H : ι → Type*)
    [∀ r, AddCommGroup (H r)] [∀ r, Module ℝ (H r)] where
  /-- Action of a degree on the moduli. -/
  modulus : ℕ → ι → ι
  /-- The framed power pullback. -/
  pull (n : ℕ) (r : ι) : H r →ₗ[ℝ] H (modulus n r)
  /-- The framed power pushforward. -/
  push (n : ℕ) (r : ι) : H (modulus n r) →ₗ[ℝ] H r
  /-- The Poincaré pairing. -/
  pairing (r : ι) : H r →ₗ[ℝ] H r →ₗ[ℝ] ℝ
  /-- The odd Hodge operator. -/
  hodge (r : ι) : H r →ₗ[ℝ] H r
  /-- Projection-formula adjunction. -/
  adjunction (n : ℕ) (r : ι) (x : H r) (z : H (modulus n r)) :
    pairing (modulus n r) (pull n r x) z = pairing r x (push n r z)
  /-- Hodge naturality. -/
  hodgeNatural (n : ℕ) (r : ι) (y : H r) :
    hodge (modulus n r) (pull n r y) = pull n r (hodge r y)
  /-- The push--pull degree law. -/
  degree (n : ℕ) (r : ι) (y : H r) : push n r (pull n r y) = (n : ℝ) • y

namespace DeningerPolarizedTransfer

variable (T : DeningerPolarizedTransfer ι H)

/-- The cup--Hodge metric `g_r(x,y) = B_r(x, J_r y)`. -/
def metric (r : ι) (x y : H r) : ℝ := T.pairing r x (T.hodge r y)

/-- **Degree scaling of the polarized metric.**  `g_{nr}(V_n x, V_n y) = n g_r(x,y)`. -/
theorem metric_pull (n : ℕ) (r : ι) (x y : H r) :
    T.metric (T.modulus n r) (T.pull n r x) (T.pull n r y) = (n : ℝ) * T.metric r x y := by
  rw [metric, metric, T.hodgeNatural, T.adjunction, T.degree, map_smul, smul_eq_mul]

/-- The half-density normalized transfer `U_n = n^{-1/2} V_n`. -/
noncomputable def normalized (n : ℕ) (r : ι) : H r →ₗ[ℝ] H (T.modulus n r) :=
  (Real.sqrt n)⁻¹ • T.pull n r

theorem normalized_apply (n : ℕ) (r : ι) (x : H r) :
    T.normalized n r x = (Real.sqrt n)⁻¹ • T.pull n r x := rfl

/-- **The half-density normalized transfer is an isometry** for the polarized metric. -/
theorem metric_normalized {n : ℕ} (hn : 0 < n) (r : ι) (x y : H r) :
    T.metric (T.modulus n r) (T.normalized n r x) (T.normalized n r y) = T.metric r x y := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : Real.sqrt n ≠ 0 := deningerSqrtNatCast_ne_zero hn
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn'.le
  have hscale : (Real.sqrt n)⁻¹ * ((Real.sqrt n)⁻¹ * (n : ℝ)) = 1 := by
    have hgroup : (Real.sqrt n)⁻¹ * ((Real.sqrt n)⁻¹ * (n : ℝ))
        = (Real.sqrt n * Real.sqrt n)⁻¹ * (n : ℝ) := by
      rw [mul_inv]; ring
    rw [hgroup, hsq, inv_mul_cancel₀ hn'.ne']
  rw [metric, metric, normalized_apply, normalized_apply, map_smul, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [show T.pairing (T.modulus n r) (T.pull n r x) (T.hodge (T.modulus n r) (T.pull n r y))
      = (n : ℝ) * T.metric r x y from T.metric_pull n r x y]
  have hfin : (Real.sqrt n)⁻¹ * ((Real.sqrt n)⁻¹ * ((n : ℝ) * T.metric r x y))
      = ((Real.sqrt n)⁻¹ * ((Real.sqrt n)⁻¹ * (n : ℝ))) * T.metric r x y := by ring
  rw [hfin, hscale, one_mul]
  rfl

/-- **Multiplicativity of the normalization.**  Wherever the pullbacks compose, so do their
half-density normalizations: transporting the composite `U_m U_n` along the modulus identity
gives `U_{mn}`. -/
theorem normalized_comp {m n : ℕ} (r : ι)
    (hmod : T.modulus m (T.modulus n r) = T.modulus (m * n) r)
    (hcomp : ∀ y : H r,
      deningerModulusCast H hmod (T.pull m (T.modulus n r) (T.pull n r y))
        = T.pull (m * n) r y)
    (x : H r) :
    deningerModulusCast H hmod (T.normalized m (T.modulus n r) (T.normalized n r x))
      = T.normalized (m * n) r x := by
  have hm' : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hsqrt : Real.sqrt ((m * n : ℕ) : ℝ) = Real.sqrt m * Real.sqrt n := by
    rw [show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) by push_cast; ring, Real.sqrt_mul hm']
  rw [normalized_apply, normalized_apply, normalized_apply, map_smul,
    deningerModulusCast_smul, deningerModulusCast_smul, hcomp, smul_smul, hsqrt, mul_inv]

/-- **The half-density factorization.**  At discrete time `t = log n` the unnormalized transfer
is `e^{t/2}` times the isometry `U_n`.  This is Deninger's weight-one half shift, obtained from
degree and adjunction alone. -/
theorem pull_eq_expHalfLog_smul_normalized {n : ℕ} (hn : 0 < n) (r : ι) (x : H r) :
    T.pull n r x = Real.exp (Real.log n / 2) • T.normalized n r x := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : Real.sqrt n ≠ 0 := deningerSqrtNatCast_ne_zero hn
  have hexp : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn']
    congr 1
    ring
  rw [hexp, normalized_apply, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- The unnormalized transfer scales the polarized metric by `e^{t}` at `t = log n`. -/
theorem metric_pull_eq_exp_log {n : ℕ} (hn : 0 < n) (r : ι) (x y : H r) :
    T.metric (T.modulus n r) (T.pull n r x) (T.pull n r y)
      = Real.exp (Real.log n) * T.metric r x y := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [T.metric_pull, Real.exp_log hn']

end DeningerPolarizedTransfer

end HalfDensity

end RHTower
