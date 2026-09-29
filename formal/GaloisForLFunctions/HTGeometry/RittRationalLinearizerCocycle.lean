import GaloisForLFunctions.HTGeometry.RationalInvariantProjectiveConnections
import GaloisForLFunctions.HTGeometry.RittLogSeedNormalForm
import GaloisForLFunctions.HTGeometry.RittLogDerivativeEigen
import GaloisForLFunctions.HTGeometry.RittDifferentialAlgebraicBridge
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.RittTreeChannelDegree

/-!
# Ritt's implication for a rational map

Let `Fr` be a Ritt frame over `k(x)` (with `k` algebraically closed of characteristic zero) whose
base
shift is substitution by a rational map `R` of degree at least two, whose base derivation is `d/dx`
and whose chain-rule factor is `R'`.

* **Degree two.**  `R'' ≠ 0` and the Schwarzian `S(R) ≠ 0`: a map with `R'' = 0` is affine, and a
map
  with `S(R) = 0` is Möbius.
* **The three normal forms become invariant objects of `R`.**  A power `v^M` in the base is an
  invariant `M`-differential, `u + c·v` in the base is an invariant affine connection, and
  `d u − u²/2 = γ + κ v²` makes `γ` an invariant projective connection.
* **The cocycle.**  Hence a differentially algebraic log seed forces a rational cocycle
  `A(R)·R'^N = β·A` with `N ≥ 1`, `β ≠ 0`, `A ≠ 0`, provided `R` has a fixed point whose multiplier
  is
  nonzero and not a root of unity (used to rigidify the projective case).
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : Type*} [Field k] [CharZero k]

/-! ### Maps of degree at least two -/

theorem eq_C_of_ratFuncDeriv_eq_zero [IsAlgClosed k] {f : RatFunc k} (h : ratFuncDeriv f = 0) :
    ∃ c : k, f = RatFunc.C c := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, by rw [map_zero]⟩
  obtain ⟨c, -, hc⟩ := eq_C_of_logDerivRat_eq_zero hf (by rw [logDerivRat, h, zero_div])
  exact ⟨c, hc⟩

theorem ratFuncDeriv_sub' (f g : RatFunc k) :
    ratFuncDeriv (f - g) = ratFuncDeriv f - ratFuncDeriv g := by
  rw [← ratFuncDerivation_apply, map_sub, ratFuncDerivation_apply, ratFuncDerivation_apply]

theorem ratFuncDeriv_inv' {f : RatFunc k} (hf : f ≠ 0) :
    ratFuncDeriv f⁻¹ = -ratFuncDeriv f / f ^ 2 := by
  rw [inv_eq_one_div, ratFuncDeriv_div_general hf, ← ratFuncDerivation_apply 1,
    Derivation.map_one_eq_zero]
  ring

/-- **A map of degree at least two has `R'' ≠ 0`.** -/
theorem deriv_deriv_ne_zero_of_two_le [IsAlgClosed k] {R : RatFunc k}
    (hd : 2 ≤ ratFuncDegree R) :
    ratFuncDeriv (ratFuncDeriv R) ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := eq_C_of_ratFuncDeriv_eq_zero h
  have h2 : ratFuncDeriv (R - RatFunc.C c * RatFunc.X) = 0 := by
    rw [ratFuncDeriv_sub', hc, ratFuncDeriv_mul, ratFuncDeriv_X, ratFuncDeriv_C]
    ring
  obtain ⟨e, he⟩ := eq_C_of_ratFuncDeriv_eq_zero h2
  have hReq : R = algebraMap k[X] (RatFunc k) (Polynomial.C c * Polynomial.X + Polynomial.C e) := by
    rw [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X, ← he]
    ring
  rw [hReq, ratFuncDegree_algebraMap] at hd
  have := natDegree_linear_le (a := c) (b := e)
  omega

/-- **A map of degree at least two has nonzero Schwarzian.** -/
theorem schwarzRat_ne_zero_of_two_le [IsAlgClosed k] {R : RatFunc k}
    (hR : ¬ ∃ c : k, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R) : schwarzRat R ≠ 0 := by
  intro hS
  have hR' := ratFuncDeriv_ne_zero_of_nonconst' hR
  have hR'' := deriv_deriv_ne_zero_of_two_le hd
  set ℓ := logDerivRat (ratFuncDeriv R) with hℓdef
  have hℓ0 : ℓ ≠ 0 := div_ne_zero hR'' hR'
  have hℓ' : ratFuncDeriv ℓ = ℓ ^ 2 / 2 := by
    rw [schwarzRat, sub_eq_zero] at hS
    exact hS
  have h2 : (2 : RatFunc k) ≠ 0 := by
    have : RatFunc.C (2 : k) ≠ 0 := by simp
    rwa [map_ofNat] at this
  have hX2 : ratFuncDeriv (RatFunc.X / 2 : RatFunc k) = 1 / 2 := by
    rw [ratFuncDeriv_div_general h2, ratFuncDeriv_X,
      show ratFuncDeriv (2 : RatFunc k) = 0 by
        rw [← map_ofNat RatFunc.C 2]; exact ratFuncDeriv_C 2]
    field_simp
    ring
  have hw : ratFuncDeriv (ℓ⁻¹ + RatFunc.X / 2) = 0 := by
    rw [ratFuncDeriv_add, ratFuncDeriv_inv' hℓ0, hℓ', hX2]
    field_simp
    ring
  obtain ⟨e, he⟩ := eq_C_of_ratFuncDeriv_eq_zero hw
  set z₀ : k := 2 * e with hz₀
  have hℓeq : ℓ = -2 * (ratLinFac z₀)⁻¹ := by
    have hinv : ℓ⁻¹ = -(ratLinFac z₀) / 2 := by
      have : ℓ⁻¹ = RatFunc.C e - RatFunc.X / 2 := by rw [← he]; ring
      rw [this, ratLinFac, hz₀, map_mul, map_ofNat]
      ring
    have h2 : ℓ = (ℓ⁻¹)⁻¹ := (inv_inv ℓ).symm
    rw [h2, hinv]
    have hl := ratLinFac_ne_zero z₀
    field_simp
  have hL : logDerivRat (ratFuncDeriv R / ratLinFac z₀ ^ (-2 : ℤ)) = 0 := by
    have hz := zpow_ne_zero (-2 : ℤ) (ratLinFac_ne_zero z₀)
    rw [div_eq_mul_inv, logDerivRat_mul hR' (inv_ne_zero hz), logDerivRat_inv hz,
      logDerivRat_zpow_linFac, ← hℓdef, hℓeq]
    push_cast
    ring
  obtain ⟨κ, hκ0, hκ⟩ := eq_C_of_logDerivRat_eq_zero
    (div_ne_zero hR' (zpow_ne_zero _ (ratLinFac_ne_zero z₀))) hL
  have hR'eq : ratFuncDeriv R = RatFunc.C κ * (ratLinFac z₀ ^ 2)⁻¹ := by
    have hz := zpow_ne_zero (-2 : ℤ) (ratLinFac_ne_zero z₀)
    rw [div_eq_iff hz] at hκ
    rw [hκ, zpow_neg, zpow_ofNat]
  have hM : ratFuncDeriv (R + RatFunc.C κ * (ratLinFac z₀)⁻¹) = 0 := by
    rw [ratFuncDeriv_add, ratFuncDeriv_mul, ratFuncDeriv_inv_linFac, ratFuncDeriv_C, hR'eq]
    ring
  obtain ⟨e', he'⟩ := eq_C_of_ratFuncDeriv_eq_zero hM
  have hlin : ¬ ∃ c : k, ratLinFac z₀ = RatFunc.C c :=
    fun ⟨c, hc⟩ => nonconst_X ⟨c + z₀, by rw [map_add, ← hc, ratLinFac]; ring⟩
  set P : RatFunc k := RatFunc.C e' - RatFunc.C κ * invX with hP
  have hReq : R = ratFuncSubstitutionAlgHom (ratLinFac z₀) hlin P := by
    rw [hP, map_sub, map_mul, ratFuncSubstitutionAlgHom_C, ratFuncSubstitutionAlgHom_C,
      subst_invX_eq_inv hlin, ← he']
    ring
  have hPeq : P = ratFuncSubstitutionAlgHom invX nonconst_invX
      (algebraMap k[X] (RatFunc k) (Polynomial.C (-κ) * Polynomial.X + Polynomial.C e')) := by
    rw [hP, map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_add, map_mul, ratFuncSubstitutionAlgHom_C, ratFuncSubstitutionAlgHom_C,
      ratFuncSubstitutionAlgHom_X, map_neg]
    ring
  have hdegP : ratFuncDegree P = 1 := by
    rw [hPeq, ratFuncDegree_substitution, ratFuncDegree_algebraMap,
      natDegree_linear (neg_ne_zero.mpr hκ0), ratFuncDegree_invX]
  have hlindeg : ratFuncDegree (ratLinFac z₀) = 1 := ratFuncDegree_X_sub_C z₀
  rw [hReq, ratFuncDegree_substitution, hdegP, hlindeg] at hd
  omega

/-- The Schwarzian in terms of `b = −R''/R'²`: `R'·b' − R'²·b²/2 = −S(R)`. -/
theorem schwarzRat_eq_of_logSeedConst {R : RatFunc k} (hR' : ratFuncDeriv R ≠ 0) :
    ratFuncDeriv R * ratFuncDeriv (-(ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2)
      - ratFuncDeriv R ^ 2 * (-(ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2) ^ 2 / 2
      = -schwarzRat R := by
  have hsq : ratFuncDeriv R ^ 2 ≠ 0 := pow_ne_zero 2 hR'
  have hneg : ratFuncDeriv (-(ratFuncDeriv (ratFuncDeriv R)))
      = -ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R)) := by
    rw [← ratFuncDerivation_apply, map_neg, ratFuncDerivation_apply]
  have hsqd : ratFuncDeriv (ratFuncDeriv R ^ 2)
      = 2 * ratFuncDeriv R * ratFuncDeriv (ratFuncDeriv R) := by
    rw [pow_two, ratFuncDeriv_mul]
    ring
  have hb' : ratFuncDeriv (-(ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2)
      = (-ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R)) * ratFuncDeriv R ^ 2
        + ratFuncDeriv (ratFuncDeriv R) * (2 * ratFuncDeriv R * ratFuncDeriv (ratFuncDeriv R)))
          / (ratFuncDeriv R ^ 2) ^ 2 := by
    rw [ratFuncDeriv_div_general hsq, hneg, hsqd]
    ring
  have hl' : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R) / ratFuncDeriv R)
      = (ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R)) * ratFuncDeriv R
        - ratFuncDeriv (ratFuncDeriv R) * ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2 :=
    ratFuncDeriv_div_general hR'
  rw [schwarzRat, logDerivRat, hl', hb']
  field_simp
  ring

/-! ### Rational Ritt frames -/

variable {L : Type*} [Field L] [Algebra (RatFunc k) L]

/-- A Ritt frame over `k(x)` whose base shift is substitution by `R`, whose base derivation is
`d/dx`, and whose chain-rule factor is `R'`. -/
structure RittFrame.IsRational (Fr : RittFrame (RatFunc k) L) (R : RatFunc k)
    (hR : ¬ ∃ c : k, R = RatFunc.C c) : Prop where
  psi : ∀ a, Fr.ψ a = ratFuncSubstitutionAlgHom R hR a
  dK : ∀ a, Fr.dK a = ratFuncDeriv a
  rho : Fr.ρ = ratFuncDeriv R

namespace RittFrame.IsRational

variable {Fr : RittFrame (RatFunc k) L} {R : RatFunc k} {hR : ¬ ∃ c : k, R = RatFunc.C c}

/-- **An invariant power of the eigen-coordinate is an invariant differential.** -/
theorem transport_of_power (hFr : Fr.IsRational R hR) {v : L}
    (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) {M : ℕ} {a : RatFunc k}
    (ha : v ^ M = algebraMap (RatFunc k) L a) :
    a ≠ 0 ∧ IsRatAffineTransport R hR (M : ℤ) 1 0 a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero M hv0 ha
  refine ⟨ha0, ?_⟩
  have h := congrArg Fr.σ ha
  rw [map_pow, hv, Fr.comp, mul_pow, ← map_pow, ha, ← map_mul] at h
  have hψ := ((algebraMap (RatFunc k) L).injective h).symm
  rw [hFr.psi, hFr.rho] at hψ
  have hR' : ratFuncDeriv R ≠ 0 := hFr.rho ▸ Fr.ρ_ne
  rw [IsRatAffineTransport, hψ, zpow_natCast, inv_pow]
  field_simp
  ring

/-- **An affine connection of the frame lying in the base is invariant.** -/
theorem connPull_eq (hFr : Fr.IsRational R hR) {u v : L} {b : RatFunc k}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2)
    (hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u + algebraMap (RatFunc k) L b)
    (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v) {c a : RatFunc k} (hc : Fr.ψ c = c)
    (ha : u + algebraMap (RatFunc k) L c * v = algebraMap (RatFunc k) L a) :
    connPull R hR a = a := by
  have h := congrArg Fr.σ ha
  rw [map_add, map_mul, Fr.comp, Fr.comp, hu, hv, hc] at h
  have key : algebraMap (RatFunc k) L (Fr.ψ a)
      = algebraMap (RatFunc k) L (Fr.ρ⁻¹ * a + b) := by
    rw [map_add, map_mul, ← ha]
    linear_combination -h
  have hψa := (algebraMap (RatFunc k) L).injective key
  have hR' : ratFuncDeriv R ≠ 0 := hFr.rho ▸ Fr.ρ_ne
  rw [hFr.psi, hFr.rho] at hψa
  rw [hFr.dK, hFr.rho] at hb
  rw [connPull, hψa, hb, logDerivRat]
  field_simp
  ring

/-- **A projective connection of the frame lying in the base is invariant.** -/
theorem projPull_eq (hFr : Fr.IsRational R hR) {u v : L} {b : RatFunc k}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2)
    (hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u + algebraMap (RatFunc k) L b)
    (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v) {γ κ : RatFunc k} (hκ : Fr.ψ κ = κ)
    (hS : Fr.d u - u ^ 2 / 2 = algebraMap (RatFunc k) L γ + algebraMap (RatFunc k) L κ * v ^ 2) :
    projPull R hR γ = γ := by
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap (RatFunc k) L).injective
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hR' : ratFuncDeriv R ≠ 0 := hFr.rho ▸ hρ0
  set r := algebraMap (RatFunc k) L Fr.ρ with hr
  have hr0 : r ≠ 0 := (map_ne_zero_iff _ (algebraMap (RatFunc k) L).injective).mpr hρ0
  have hrinv : algebraMap (RatFunc k) L Fr.ρ⁻¹ = r⁻¹ := map_inv₀ _ _
  -- the derivative of `σ u`
  have hdKinv : Fr.dK Fr.ρ⁻¹ = b := by rw [Fr.dK_inv hρ0, hb]
  have h1 : Fr.d (Fr.σ u) = algebraMap (RatFunc k) L b * u + r⁻¹ * Fr.d u
      + algebraMap (RatFunc k) L (Fr.dK b) := by
    rw [hu, Fr.d_add, Fr.d_mul, Fr.d_base, Fr.d_base, hdKinv, hrinv]
  have hchain : r * Fr.σ (Fr.d u) = algebraMap (RatFunc k) L b * u + r⁻¹ * Fr.d u
      + algebraMap (RatFunc k) L (Fr.dK b) := by
    rw [← h1, Fr.chain]
  -- apply the shift to the Schwarzian relation
  have h2 := congrArg Fr.σ hS
  rw [map_sub, map_div₀, map_pow, map_ofNat, map_add, map_mul, map_pow, Fr.comp, Fr.comp, hκ,
    hu, hv, hrinv] at h2
  have hdu : Fr.d u = u ^ 2 / 2 + algebraMap (RatFunc k) L γ
      + algebraMap (RatFunc k) L κ * v ^ 2 := by
    linear_combination hS
  have key : algebraMap (RatFunc k) L (Fr.ψ γ)
      = algebraMap (RatFunc k) L (Fr.ρ⁻¹ ^ 2 * γ + Fr.ρ⁻¹ * Fr.dK b - b ^ 2 / 2) := by
    rw [map_sub, map_add, map_mul, map_mul, map_pow, hrinv, map_div₀, map_pow, map_ofNat]
    have hσdu : Fr.σ (Fr.d u) = r⁻¹ * (algebraMap (RatFunc k) L b * u + r⁻¹ * Fr.d u
        + algebraMap (RatFunc k) L (Fr.dK b)) := by
      rw [← hchain]; field_simp
    rw [hσdu, hdu] at h2
    linear_combination -h2
  have hψγ := (algebraMap (RatFunc k) L).injective key
  rw [hFr.psi, hFr.rho, hFr.dK] at hψγ
  rw [hFr.dK, hFr.rho] at hb
  have hid := schwarzRat_eq_of_logSeedConst hR'
  rw [← hb] at hid
  rw [projPull, hψγ]
  field_simp
  linear_combination 2 * hid

/-- **An invariant affine connection yields a cocycle with a nonzero constant.** -/
theorem _root_.GaloisForLFunctions.HTGeometry.ratTransport_of_invariant_connection
    [IsAlgClosed k] (hR : ¬ ∃ c : k, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    {a : RatFunc k} (ha : connPull R hR a = a) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : k, β ≠ 0 ∧ ∃ A : RatFunc k, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  obtain ⟨N, hN, g, hg, hga⟩ := exists_logDeriv_of_invariant_connection hR hd ha
  obtain ⟨κ, hκ0, hκ⟩ := exists_const_of_logDeriv hR ha hg hga
  refine ⟨N, hN, κ⁻¹, inv_ne_zero hκ0, g, hg, ?_⟩
  have hC : RatFunc.C κ ≠ 0 := by simpa using hκ0
  rw [IsRatAffineTransport, zpow_natCast, add_zero, map_inv₀]
  conv_rhs => rw [hκ]
  field_simp

/-- **Ritt's implication for a rational map, for a log seed.**  A differentially algebraic log seed
of a rational frame forces a rational cocycle `A(R)·R'^N = β·A`. -/
theorem ratTransport_of_logSeed [IsAlgClosed k] (hFr : Fr.IsRational R hR)
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1)
    {u v : L} {b : RatFunc k} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2)
    (hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u + algebraMap (RatFunc k) L b)
    (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hDA : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u)) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : k, β ≠ 0 ∧ ∃ A : RatFunc k, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  classical
  have hR' : ratFuncDeriv R ≠ 0 := hFr.rho ▸ Fr.ρ_ne
  have hb' : b = -(ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2 := by
    rw [hb, hFr.dK, hFr.rho]
  have hb0 : b ≠ 0 := by
    rw [hb']
    exact div_ne_zero (neg_ne_zero.mpr (deriv_deriv_ne_zero_of_two_le hd)) (pow_ne_zero 2 hR')
  have hS : Fr.logConst b 1 ≠ b ^ 2 / 2 := by
    show Fr.ρ⁻¹ * Fr.dK b ≠ b ^ 2 / 2
    intro h
    rw [hFr.rho, hFr.dK] at h
    apply schwarzRat_ne_zero_of_two_le hR hd
    have hid := schwarzRat_eq_of_logSeedConst hR'
    rw [← hb'] at hid
    have h2 : ratFuncDeriv R * ratFuncDeriv b = ratFuncDeriv R ^ 2 * (b ^ 2 / 2) := by
      rw [← h]
      field_simp
    linear_combination hid - h2
  rcases Fr.normalForm_of_differentiallyAlgebraic hb hb0 hS hu hv hv0 hdv hDA with
    ⟨M, hM, a, ha⟩ | ⟨c, a, hc, ha⟩ | ⟨γ, κ, hκ, hSγ⟩
  · obtain ⟨ha0, htr⟩ := hFr.transport_of_power hv hv0 ha
    exact ⟨M, hM, 1, one_ne_zero, a, ha0, by rw [map_one]; exact htr⟩
  · exact ratTransport_of_invariant_connection hR hd (hFr.connPull_eq hb hu hv hc ha)
  · obtain ⟨a, ha, -⟩ := exists_schConn_of_invariant_projective hR hd h0 hR0 hlam0 hlam
      (hFr.projPull_eq hb hu hv hκ hSγ)
    exact ratTransport_of_invariant_connection hR hd ha

/-- **Ritt's implication for a rational map, for a linearizer.**  If `σ τ = q·τ` with `q` a nonzero
constant, `d τ ≠ 0`, and `τ` is differentially algebraic over `k(x)`, then `R` carries a rational
cocycle `A(R)·R'^N = β·A` with `N ≥ 1`, `β ≠ 0`, `A ≠ 0`. -/
theorem ratTransport_of_linearizer [IsAlgClosed k] [Differential (RatFunc k)] [Differential L]
    [DifferentialAlgebra (RatFunc k) L] (hFr : Fr.IsRational R hR)
    (hdiff : Fr.d = ⇑(Differential.deriv : Derivation ℤ L L))
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1)
    {τ : L} {q : k} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0)
    (hshift : Fr.σ τ = algebraMap (RatFunc k) L (RatFunc.C q) * τ)
    (hDA : DifferentialAlgebraicOver (RatFunc k) τ) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : k, β ≠ 0 ∧ ∃ A : RatFunc k, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap (RatFunc k) L).injective
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hCq : (RatFunc.C q : RatFunc k) ≠ 0 := by simpa using hq
  set v := Fr.d τ / τ with hvdef
  have hv0 : v ≠ 0 := div_ne_zero hdτ hτ
  have hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v := by
    have h := sigma_logDeriv_of_eigen Fr hτ hCq hshift
    rw [hFr.dK, ratFuncDeriv_C, zero_div, map_zero, add_zero] at h
    exact h
  set u := Fr.d v / v with hudef
  have hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u
      + algebraMap (RatFunc k) L (-(Fr.dK Fr.ρ) / Fr.ρ ^ 2) := by
    have h := sigma_logDeriv_of_eigen Fr hv0 (inv_ne_zero hρ0) hv
    rw [mul_inv_cancel₀ hρ0, div_one, Fr.dK_inv hρ0] at h
    exact h
  have hdv : Fr.d v = u * v := by rw [hudef]; field_simp
  -- the log seed is differentially algebraic
  have hmem : u ∈ differentialAdjoin (RatFunc k) ({τ} : Set L) := by
    set F := differentialAdjoin (RatFunc k) ({τ} : Set L)
    have hcl := derivationClosed_differentialAdjoin (RatFunc k) ({τ} : Set L)
    have hdmem : ∀ x ∈ F, Fr.d x ∈ F := fun x hx => by rw [hdiff]; exact hcl hx
    have hτF : τ ∈ F := subset_differentialAdjoin (RatFunc k) ({τ} : Set L) rfl
    have hvF : v ∈ F := F.div_mem (hdmem τ hτF) hτF
    exact F.div_mem (hdmem v hvF) hvF
  have hDAu := differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hDA hmem
  obtain ⟨n, hn⟩ := exists_algebraic_jet_over_prefix (k := RatFunc k) hDAu
  have hjet : Fr.d^[n] u = differentialJet n u := by simp [differentialJet, hdiff]
  have hDA' : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u) := by
    refine ⟨n, ?_⟩
    rw [jetPrefixField_eq_differentialJetPrefixField Fr hdiff, hjet]
    exact hn
  exact ratTransport_of_logSeed hFr hd h0 hR0 hlam0 hlam rfl hu hv hv0 hdv hDA'

/-- **Ritt's implication for a rational map, with the multiplier.**  A differentially algebraic log
seed of a rational frame forces the cocycle `R'^N·B = λ^{N+j}·B(R)` with `λ = R'(0)`. -/
theorem ratCocycle_of_logSeed [IsAlgClosed k] (hFr : Fr.IsRational R hR)
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1)
    {u v : L} {b : RatFunc k} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2)
    (hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u + algebraMap (RatFunc k) L b)
    (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hDA : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u)) :
    ∃ N : ℕ, 0 < N ∧ ∃ j : ℤ, ∃ B : RatFunc k, B ≠ 0 ∧
      ratFuncDeriv R ^ N * B
        = RatFunc.C (ratValue (ratFuncDeriv R) 0 ^ ((N : ℤ) + j))
          * ratFuncSubstitutionAlgHom R hR B := by
  classical
  have hR' : ratFuncDeriv R ≠ 0 := hFr.rho ▸ Fr.ρ_ne
  have hb' : b = -(ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2 := by
    rw [hb, hFr.dK, hFr.rho]
  have hb0 : b ≠ 0 := by
    rw [hb']
    exact div_ne_zero (neg_ne_zero.mpr (deriv_deriv_ne_zero_of_two_le hd)) (pow_ne_zero 2 hR')
  have hS : Fr.logConst b 1 ≠ b ^ 2 / 2 := by
    show Fr.ρ⁻¹ * Fr.dK b ≠ b ^ 2 / 2
    intro h
    rw [hFr.rho, hFr.dK] at h
    apply schwarzRat_ne_zero_of_two_le hR hd
    have hid := schwarzRat_eq_of_logSeedConst hR'
    rw [← hb'] at hid
    have h2 : ratFuncDeriv R * ratFuncDeriv b = ratFuncDeriv R ^ 2 * (b ^ 2 / 2) := by
      rw [← h]
      field_simp
    linear_combination hid - h2
  rcases Fr.normalForm_of_differentiallyAlgebraic hb hb0 hS hu hv hv0 hdv hDA with
    ⟨M, hM, a, ha⟩ | ⟨c, a, hc, ha⟩ | ⟨γ, κ, hκ, hSγ⟩
  · obtain ⟨ha0, htr⟩ := hFr.transport_of_power hv hv0 ha
    refine ⟨M, hM, -(M : ℤ), a⁻¹, inv_ne_zero ha0, ?_⟩
    rw [add_neg_cancel, zpow_zero, map_one, one_mul, map_inv₀]
    rw [IsRatAffineTransport, zpow_natCast, one_mul, add_zero] at htr
    have hsa : ratFuncSubstitutionAlgHom R hR a ≠ 0 := by
      intro h0
      exact ha0 ((ratFuncSubstitutionAlgHom R hR).toRingHom.injective (by simpa using h0))
    conv_lhs => rw [← htr]
    field_simp
  · exact ratCocycle_of_invariant_connection hR hd h0 hR0 hlam0 (hFr.connPull_eq hb hu hv hc ha)
  · obtain ⟨a, ha, -⟩ := exists_schConn_of_invariant_projective hR hd h0 hR0 hlam0 hlam
      (hFr.projPull_eq hb hu hv hκ hSγ)
    exact ratCocycle_of_invariant_connection hR hd h0 hR0 hlam0 ha

/-- **Ritt's implication for a rational map, for a linearizer, with the multiplier.** -/
theorem ratCocycle_of_linearizer [IsAlgClosed k] [Differential (RatFunc k)] [Differential L]
    [DifferentialAlgebra (RatFunc k) L] (hFr : Fr.IsRational R hR)
    (hdiff : Fr.d = ⇑(Differential.deriv : Derivation ℤ L L))
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1)
    {τ : L} {q : k} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0)
    (hshift : Fr.σ τ = algebraMap (RatFunc k) L (RatFunc.C q) * τ)
    (hDA : DifferentialAlgebraicOver (RatFunc k) τ) :
    ∃ N : ℕ, 0 < N ∧ ∃ j : ℤ, ∃ B : RatFunc k, B ≠ 0 ∧
      ratFuncDeriv R ^ N * B
        = RatFunc.C (ratValue (ratFuncDeriv R) 0 ^ ((N : ℤ) + j))
          * ratFuncSubstitutionAlgHom R hR B := by
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap (RatFunc k) L).injective
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hCq : (RatFunc.C q : RatFunc k) ≠ 0 := by simpa using hq
  set v := Fr.d τ / τ with hvdef
  have hv0 : v ≠ 0 := div_ne_zero hdτ hτ
  have hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v := by
    have h := sigma_logDeriv_of_eigen Fr hτ hCq hshift
    rw [hFr.dK, ratFuncDeriv_C, zero_div, map_zero, add_zero] at h
    exact h
  set u := Fr.d v / v with hudef
  have hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u
      + algebraMap (RatFunc k) L (-(Fr.dK Fr.ρ) / Fr.ρ ^ 2) := by
    have h := sigma_logDeriv_of_eigen Fr hv0 (inv_ne_zero hρ0) hv
    rw [mul_inv_cancel₀ hρ0, div_one, Fr.dK_inv hρ0] at h
    exact h
  have hdv : Fr.d v = u * v := by rw [hudef]; field_simp
  have hmem : u ∈ differentialAdjoin (RatFunc k) ({τ} : Set L) := by
    set F := differentialAdjoin (RatFunc k) ({τ} : Set L)
    have hcl := derivationClosed_differentialAdjoin (RatFunc k) ({τ} : Set L)
    have hdmem : ∀ x ∈ F, Fr.d x ∈ F := fun x hx => by rw [hdiff]; exact hcl hx
    have hτF : τ ∈ F := subset_differentialAdjoin (RatFunc k) ({τ} : Set L) rfl
    have hvF : v ∈ F := F.div_mem (hdmem τ hτF) hτF
    exact F.div_mem (hdmem v hvF) hvF
  have hDAu := differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hDA hmem
  obtain ⟨n, hn⟩ := exists_algebraic_jet_over_prefix (k := RatFunc k) hDAu
  have hjet : Fr.d^[n] u = differentialJet n u := by simp [differentialJet, hdiff]
  have hDA' : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u) := by
    refine ⟨n, ?_⟩
    rw [jetPrefixField_eq_differentialJetPrefixField Fr hdiff, hjet]
    exact hn
  exact ratCocycle_of_logSeed hFr hd h0 hR0 hlam0 hlam rfl hu hv hv0 hdv hDA'

/-- **Ritt's implication for a rational map, for a log seed, without a fixed point.**  The
exclusion form: a differentially algebraic log seed of a rational frame forces a rational cocycle
`A(R)·R'^N = β·A` with `β ≠ 0`; the projective case goes through the orbifold connection, which
needs
no fixed point. -/
theorem ratTransport_of_logSeed_of_noFixedPoint [IsAlgClosed k] (hFr : Fr.IsRational R hR)
    (hd : 2 ≤ ratFuncDegree R) {u v : L} {b : RatFunc k} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2)
    (hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u + algebraMap (RatFunc k) L b)
    (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hDA : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u)) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : k, β ≠ 0 ∧ ∃ A : RatFunc k, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  classical
  have hR' : ratFuncDeriv R ≠ 0 := hFr.rho ▸ Fr.ρ_ne
  have hb' : b = -(ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R ^ 2 := by
    rw [hb, hFr.dK, hFr.rho]
  have hb0 : b ≠ 0 := by
    rw [hb']
    exact div_ne_zero (neg_ne_zero.mpr (deriv_deriv_ne_zero_of_two_le hd)) (pow_ne_zero 2 hR')
  have hS : Fr.logConst b 1 ≠ b ^ 2 / 2 := by
    show Fr.ρ⁻¹ * Fr.dK b ≠ b ^ 2 / 2
    intro h
    rw [hFr.rho, hFr.dK] at h
    apply schwarzRat_ne_zero_of_two_le hR hd
    have hid := schwarzRat_eq_of_logSeedConst hR'
    rw [← hb'] at hid
    have h2 : ratFuncDeriv R * ratFuncDeriv b = ratFuncDeriv R ^ 2 * (b ^ 2 / 2) := by
      rw [← h]
      field_simp
    linear_combination hid - h2
  rcases Fr.normalForm_of_differentiallyAlgebraic hb hb0 hS hu hv hv0 hdv hDA with
    ⟨M, hM, a, ha⟩ | ⟨c, a, hc, ha⟩ | ⟨γ, κ, hκ, hSγ⟩
  · obtain ⟨ha0, htr⟩ := hFr.transport_of_power hv hv0 ha
    exact ⟨M, hM, 1, one_ne_zero, a, ha0, by rw [map_one]; exact htr⟩
  · exact ratTransport_of_invariant_connection hR hd (hFr.connPull_eq hb hu hv hc ha)
  · obtain ⟨a, ha, -⟩ := exists_invariant_connection_of_invariant_projective hR hd
      (hFr.projPull_eq hb hu hv hκ hSγ)
    exact ratTransport_of_invariant_connection hR hd ha

/-- **Ritt's implication for an eigen-coordinate, without a fixed point.**  If `σ v = ρ⁻¹·v` with
`v ≠ 0` differentially algebraic over `k(x)`, then `R` carries a rational cocycle. -/
theorem ratTransport_of_eigen_of_noFixedPoint [IsAlgClosed k] [Differential (RatFunc k)]
    [Differential L] [DifferentialAlgebra (RatFunc k) L] (hFr : Fr.IsRational R hR)
    (hdiff : Fr.d = ⇑(Differential.deriv : Derivation ℤ L L)) (hd : 2 ≤ ratFuncDegree R)
    {v : L} (hv0 : v ≠ 0) (hv : Fr.σ v = algebraMap (RatFunc k) L Fr.ρ⁻¹ * v)
    (hDA : DifferentialAlgebraicOver (RatFunc k) v) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : k, β ≠ 0 ∧ ∃ A : RatFunc k, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap (RatFunc k) L).injective
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set u := Fr.d v / v with hudef
  have hu : Fr.σ u = algebraMap (RatFunc k) L Fr.ρ⁻¹ * u
      + algebraMap (RatFunc k) L (-(Fr.dK Fr.ρ) / Fr.ρ ^ 2) := by
    have h := sigma_logDeriv_of_eigen Fr hv0 (inv_ne_zero hρ0) hv
    rw [mul_inv_cancel₀ hρ0, div_one, Fr.dK_inv hρ0] at h
    exact h
  have hdv : Fr.d v = u * v := by rw [hudef]; field_simp
  have hmem : u ∈ differentialAdjoin (RatFunc k) ({v} : Set L) := by
    set F := differentialAdjoin (RatFunc k) ({v} : Set L)
    have hcl := derivationClosed_differentialAdjoin (RatFunc k) ({v} : Set L)
    have hvF : v ∈ F := subset_differentialAdjoin (RatFunc k) ({v} : Set L) rfl
    have hdvF : Fr.d v ∈ F := by rw [hdiff]; exact hcl hvF
    exact F.div_mem hdvF hvF
  have hDAu := differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hDA hmem
  obtain ⟨n, hn⟩ := exists_algebraic_jet_over_prefix (k := RatFunc k) hDAu
  have hjet : Fr.d^[n] u = differentialJet n u := by simp [differentialJet, hdiff]
  have hDA' : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u) := by
    refine ⟨n, ?_⟩
    rw [jetPrefixField_eq_differentialJetPrefixField Fr hdiff, hjet]
    exact hn
  exact ratTransport_of_logSeed_of_noFixedPoint hFr hd rfl hu hv hv0 hdv hDA'

end RittFrame.IsRational

end

end GaloisForLFunctions.HTGeometry
