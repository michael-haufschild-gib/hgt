import GaloisForLFunctions.HTGeometry.LieCartanFormalVectorFields
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal vector fields on a line: the normal forms of the trichotomy

A transitive finite-dimensional Lie algebra of formal vector fields on a line has rank at most
three.  This file proves the *normal-form* half of the classification, in the invariant form that
its consumers actually need: such an algebra always preserves a **projective connection**, and in
rank at most two it already preserves an **affine connection**.

A vector field `f ∂` acts on the three geometric structures of the trichotomy by

```text
δ_f η = f η′ + k f′ η              (a weight-`k` differential)
δ_f μ = f μ′ + f′ μ + f″           (an affine connection)
δ_f q = f q′ + 2 f′ q + 2 f‴       (a projective connection)
```

these being the linearizations of the three transformation laws

```text
η(y) (y′)^k = η(x),   μ(y) y′ + y″/y′ = μ(x),   q(y) (y′)² + 2y‴/y′ − 3(y″/y′)² = q(x).
```

Two mechanisms carry the whole proof.

* An affine connection is a *primitive*: `δ_f μ = (f μ + f′)′`.  So a bracket-closed pair with a
  unit member has an affine connection written down explicitly from the structure constants.
* A projective connection is a *quotient*: for any `f`, the combination `Q = (f′)² − 2 f f″`
  satisfies `Q′ = −2 f f‴` identically, hence `q = Q/f²` solves `δ_f q = 0` whenever the division
  is legitimate.  For the order-two member of a rank-three algebra the division *is* legitimate,
  because bracket-closedness forces its third coefficient to vanish.

The passage from that one field to the whole algebra is the cocycle identity

```text
δ_{[f,g]} q = ρ(f)(δ_g q) − ρ(g)(δ_f q),      ρ(f) w = f w′ + 2 f′ w ,
```

together with the observation that `ρ(u) w = 0` with `u` of order two forces `w = 0`: multiplying
by `u` turns it into `(u² w)′ = 0`, and a constant that vanishes to order four is zero.
-/

open PowerSeries

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-! ## Derivative calculus -/

/-- The Leibniz rule, in multiplicative form. -/
theorem vfDeriv_mul (f g : PowerSeries K) :
    (d⁄dX K) (f * g) = f * (d⁄dX K) g + g * (d⁄dX K) f := by
  simp [(PowerSeries.derivative (R := K)).leibniz f g, smul_eq_mul]

theorem vfDeriv_two : (d⁄dX K) (2 : PowerSeries K) = 0 := by
  have h : (2 : PowerSeries K) = 1 + 1 := by ring
  rw [h, map_add, Derivation.map_one_eq_zero]
  simp

theorem vfDeriv_X_sq : (d⁄dX K) ((X : PowerSeries K) ^ 2) = 2 * X := by
  have h : ((X : PowerSeries K) ^ 2) = X * X := by ring
  rw [h, vfDeriv_mul]
  simp
  ring

/-- The constant coefficient of a product. -/
theorem coeff_zero_mul_eq (f g : PowerSeries K) :
    coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
    coeff_zero_eq_constantCoeff_apply, map_mul]

theorem coeff_zero_X_eq : coeff 0 (X : PowerSeries K) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  simp

theorem coeff_one_X_eq : coeff 1 (X : PowerSeries K) = 1 := by simp

/-- The linear coefficient of a product. -/
theorem coeff_one_mul_eq (f g : PowerSeries K) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul]
  simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]

/-- In characteristic zero a series with vanishing derivative and vanishing constant term is
zero. -/
theorem eq_zero_of_vfDeriv_eq_zero [CharZero K] {h : PowerSeries K}
    (hd : (d⁄dX K) h = 0) (h0 : coeff 0 h = 0) : h = 0 := by
  ext n
  cases n with
  | zero => simpa using h0
  | succ n =>
      have hcoeff : coeff n ((d⁄dX K) h) = 0 := by rw [hd]; simp
      rw [coeff_derivative] at hcoeff
      have hne : ((n : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      simpa using (mul_eq_zero.mp hcoeff).resolve_right hne


/-! ## The three defects -/

/-- The infinitesimal action of a formal vector field on a weight-`k` differential. -/
def vfTensorDefect (k : K) (f η : PowerSeries K) : PowerSeries K :=
  f * (d⁄dX K) η + (k • (d⁄dX K) f) * η

/-- The infinitesimal action of a formal vector field on an affine connection. -/
def vfAffineDefect (f μ : PowerSeries K) : PowerSeries K :=
  f * (d⁄dX K) μ + (d⁄dX K) f * μ + (d⁄dX K) ((d⁄dX K) f)

/-- The infinitesimal action of a formal vector field on a projective connection. -/
def vfProjDefect (f q : PowerSeries K) : PowerSeries K :=
  f * (d⁄dX K) q + 2 * ((d⁄dX K) f * q) + 2 * (d⁄dX K) ((d⁄dX K) ((d⁄dX K) f))

/-- The weight-two Lie derivative, the linear part of the projective action. -/
def vfRho (f w : PowerSeries K) : PowerSeries K := f * (d⁄dX K) w + 2 * ((d⁄dX K) f * w)

/-- **An affine connection is a primitive.** -/
theorem vfAffineDefect_eq_deriv (f μ : PowerSeries K) :
    vfAffineDefect f μ = (d⁄dX K) (f * μ + (d⁄dX K) f) := by
  unfold vfAffineDefect
  simp only [map_add, vfDeriv_mul]
  ring

theorem vfAffineDefect_add (f g μ : PowerSeries K) :
    vfAffineDefect (f + g) μ = vfAffineDefect f μ + vfAffineDefect g μ := by
  unfold vfAffineDefect
  simp only [map_add]
  ring

theorem vfAffineDefect_smul (a : K) (f μ : PowerSeries K) :
    vfAffineDefect (a • f) μ = a • vfAffineDefect f μ := by
  unfold vfAffineDefect
  simp only [Derivation.map_smul, smul_add, smul_mul_assoc]

theorem vfProjDefect_add (f g q : PowerSeries K) :
    vfProjDefect (f + g) q = vfProjDefect f q + vfProjDefect g q := by
  unfold vfProjDefect
  simp only [map_add]
  ring

theorem vfProjDefect_smul (a : K) (f q : PowerSeries K) :
    vfProjDefect (a • f) q = a • vfProjDefect f q := by
  unfold vfProjDefect
  simp only [Derivation.map_smul, smul_add, smul_mul_assoc, mul_smul_comm]

theorem vfProjDefect_zero (q : PowerSeries K) : vfProjDefect 0 q = 0 := by
  unfold vfProjDefect
  simp

/-- **The cocycle identity.**  The projective action is an affine action of the Lie algebra: its
defect on a bracket is the commutator of the weight-two Lie derivatives of the two defects. -/
theorem vfProjDefect_vfBracket (f g q : PowerSeries K) :
    vfProjDefect (vfBracket f g) q = vfRho f (vfProjDefect g q) - vfRho g (vfProjDefect f q) := by
  unfold vfProjDefect vfRho vfBracket
  simp only [map_add, map_sub, vfDeriv_mul, vfDeriv_two, mul_zero, add_zero]
  ring

/-- **Projectivizing an affine connection.**  The projective defect of `2 μ′ − μ²` is a
first-order expression in the affine defect of `μ`, so it vanishes whenever that does. -/
theorem vfProjDefect_projectivization (f μ : PowerSeries K) :
    vfProjDefect f (2 * (d⁄dX K) μ - μ * μ) =
      2 * (d⁄dX K) (vfAffineDefect f μ) - 2 * (μ * vfAffineDefect f μ) := by
  unfold vfProjDefect vfAffineDefect
  simp only [map_add, map_sub, vfDeriv_mul, vfDeriv_two, mul_zero, add_zero]
  ring

/-! ## Rank at most two: the affine normal form -/

/-- **The affine connection of a bracket-closed pair with a unit member.**  If
`[e₀, e₁] = α e₀ + β e₁` and `e₀` is a unit, then `μ = (−β − e₀′)/e₀` is an affine connection
preserved by both fields: `e₀ μ + e₀′ = −β` and `e₁ μ + e₁′ = α` are constants. -/
theorem exists_affineConnection_of_pair {e₀ e₁ : PowerSeries K} (he₀ : coeff 0 e₀ ≠ 0) {α β : K}
    (hbr : vfBracket e₀ e₁ = α • e₀ + β • e₁) :
    ∃ μ : PowerSeries K, vfAffineDefect e₀ μ = 0 ∧ vfAffineDefect e₁ μ = 0 := by
  have hunit : constantCoeff e₀ ≠ (0 : K) := by
    rwa [← coeff_zero_eq_constantCoeff_apply]
  have hinv : e₀ * e₀⁻¹ = 1 := PowerSeries.mul_inv_cancel e₀ hunit
  refine ⟨((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) * e₀⁻¹, ?_, ?_⟩
  · have hval : e₀ * (((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) * e₀⁻¹) + (d⁄dX K) e₀
        = (-β : K) • (1 : PowerSeries K) := by
      have h : e₀ * (((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) * e₀⁻¹)
          = ((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) * (e₀ * e₀⁻¹) := by ring
      rw [h, hinv, mul_one]
      ring
    rw [vfAffineDefect_eq_deriv, hval, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
  · have hval : e₁ * (((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) * e₀⁻¹) + (d⁄dX K) e₁
        = (α : K) • (1 : PowerSeries K) := by
      have hnum : e₁ * ((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) + e₀ * (d⁄dX K) e₁
          = (α : K) • e₀ := by
        have hb : e₀ * (d⁄dX K) e₁ - (d⁄dX K) e₀ * e₁ = α • e₀ + β • e₁ := hbr
        have hsmul : e₁ * ((-β : K) • (1 : PowerSeries K)) = -(β • e₁) := by
          rw [smul_eq_C_mul, smul_eq_C_mul]
          simp [map_neg]
          ring
        rw [mul_sub, hsmul]
        rw [show -(β • e₁) - e₁ * (d⁄dX K) e₀ + e₀ * (d⁄dX K) e₁
              = (e₀ * (d⁄dX K) e₁ - (d⁄dX K) e₀ * e₁) - β • e₁ by ring, hb]
        abel
      have h : e₁ * (((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) * e₀⁻¹) + (d⁄dX K) e₁
          = (e₁ * ((-β : K) • (1 : PowerSeries K) - (d⁄dX K) e₀) + e₀ * (d⁄dX K) e₁) * e₀⁻¹
            + (d⁄dX K) e₁ * (1 - e₀ * e₀⁻¹) := by ring
      rw [h, hinv, sub_self, mul_zero, add_zero, hnum, smul_mul_assoc, hinv]
    rw [vfAffineDefect_eq_deriv, hval, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

/-! ## Rank three: the projective normal form -/

/-- **The exact primitive behind the projective quotient.**  For every formal series
`((f′)² − 2 f f″)′ = −2 f f‴`. -/
theorem deriv_projNumerator (f : PowerSeries K) :
    (d⁄dX K) ((d⁄dX K) f * (d⁄dX K) f - 2 * (f * (d⁄dX K) ((d⁄dX K) f)))
      = -(2 * (f * (d⁄dX K) ((d⁄dX K) ((d⁄dX K) f)))) := by
  simp only [map_sub, vfDeriv_mul, vfDeriv_two, mul_zero, add_zero]
  ring

/-- If `q u² = (u′)² − 2 u u″` then `u` preserves the projective connection `q`. -/
theorem vfProjDefect_eq_zero_of_quotient {u q : PowerSeries K} (hu : u ≠ 0)
    (hq : q * (u * u) = (d⁄dX K) u * (d⁄dX K) u - 2 * (u * (d⁄dX K) ((d⁄dX K) u))) :
    vfProjDefect u q = 0 := by
  have hD := congrArg (fun x : PowerSeries K => (d⁄dX K) x) hq
  simp only [vfDeriv_mul] at hD
  rw [deriv_projNumerator] at hD
  have hkey : u * vfProjDefect u q = 0 := by
    unfold vfProjDefect
    have hexp : u * (u * (d⁄dX K) q + 2 * ((d⁄dX K) u * q)
          + 2 * (d⁄dX K) ((d⁄dX K) ((d⁄dX K) u)))
        = (q * (u * (d⁄dX K) u) + (u * u * (d⁄dX K) q + q * (u * (d⁄dX K) u)))
          + 2 * (u * (d⁄dX K) ((d⁄dX K) ((d⁄dX K) u))) := by ring
    rw [hexp]
    linear_combination hD
  exact (mul_eq_zero.mp hkey).resolve_left hu

/-- If `ρ(u) w = 0` and `u` vanishes to order two, then `w = 0`: multiplying by `u` makes the
relation `(u² w)′ = 0`, and a constant vanishing to order four is zero. -/
theorem eq_zero_of_vfRho_eq_zero [CharZero K] {u w : PowerSeries K} (hu : u ≠ 0)
    (hu0 : coeff 0 u = 0) (h : vfRho u w = 0) : w = 0 := by
  have hD : (d⁄dX K) (u * u * w) = 0 := by
    have hexp : (d⁄dX K) (u * u * w) = u * (u * (d⁄dX K) w + 2 * ((d⁄dX K) u * w)) := by
      simp only [vfDeriv_mul]
      ring
    rw [hexp]
    unfold vfRho at h
    rw [h, mul_zero]
  have h0 : coeff 0 (u * u * w) = 0 := by
    have : constantCoeff (u * u * w) = (0 : K) := by
      rw [map_mul, map_mul, ← coeff_zero_eq_constantCoeff_apply, hu0]
      ring
    rwa [coeff_zero_eq_constantCoeff_apply]
  have huw : u * u * w = 0 := eq_zero_of_vfDeriv_eq_zero hD h0
  rcases mul_eq_zero.mp huw with h1 | h2
  · exact absurd ((mul_eq_zero.mp h1).elim id id) hu
  · exact h2

/-- **The order-two field of a rank-three algebra has vanishing third coefficient.**  This is the
normalization that makes the projective quotient regular, and it is forced by the single relation
`[e₁, e₂] ∈ K e₂` with `e₁` of order one and `e₂` of order two. -/
theorem coeff_three_eq_zero_of_bracket {e₁ e₂ : PowerSeries K} {lam : K}
    (h₁ : HasOrder e₁ 1) (h₂ : HasOrder e₂ 2) (hrel : vfBracket e₁ e₂ = lam • e₂) :
    coeff 3 e₂ = 0 := by
  obtain ⟨gt, hgt⟩ : (X : PowerSeries K) ∣ e₁ := by
    rw [PowerSeries.X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
    exact h₁.2 0 (by norm_num)
  obtain ⟨v, hv⟩ : (X : PowerSeries K) ^ 2 ∣ e₂ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    exact h₂.2 m hm
  have hgt0 : coeff 0 gt ≠ 0 := by
    have : coeff 1 e₁ = coeff 0 gt := by
      rw [hgt]
      simp
    rw [← this]; exact h₁.1
  have hv0 : coeff 0 v ≠ 0 := by
    have : coeff 2 e₂ = coeff 0 v := by
      rw [hv]
      simpa using PowerSeries.coeff_X_pow_mul v 2 0
    rw [← this]; exact h₂.1
  have hv1 : coeff 1 v = 0 := by
    -- the bracket relation, with the two factorizations substituted and `X²` cancelled
    have hDe₂ : (d⁄dX K) e₂ = X ^ 2 * (d⁄dX K) v + v * (2 * X) := by
      rw [hv, vfDeriv_mul, vfDeriv_X_sq]
    have hDe₁ : (d⁄dX K) e₁ = X * (d⁄dX K) gt + gt := by
      rw [hgt, vfDeriv_mul]
      simp
    have hexp : vfBracket e₁ e₂
        = X ^ 2 * (gt * v + X * (gt * (d⁄dX K) v - v * (d⁄dX K) gt)) := by
      unfold vfBracket
      rw [hDe₂, hDe₁, hgt, hv]
      ring
    have hexp2 : lam • e₂ = X ^ 2 * (lam • v) := by
      rw [hv, smul_eq_C_mul, smul_eq_C_mul]
      ring
    have hXne : ((X : PowerSeries K) ^ 2) ≠ 0 := pow_ne_zero 2 PowerSeries.X_ne_zero
    have hR : gt * v + X * (gt * (d⁄dX K) v - v * (d⁄dX K) gt) = lam • v := by
      refine mul_left_cancel₀ hXne ?_
      rw [← hexp, ← hexp2, hrel]
    have hlam : lam = coeff 0 gt := by
      have h0 := congrArg (fun x : PowerSeries K => coeff 0 x) hR
      simp only [map_add, map_smul, smul_eq_mul, coeff_zero_mul_eq, coeff_zero_X_eq,
        zero_mul] at h0
      have h0' : coeff 0 gt * coeff 0 v = lam * coeff 0 v := by linear_combination h0
      exact (mul_right_cancel₀ hv0 h0').symm
    have hDv0 : coeff 0 ((d⁄dX K) v) = coeff 1 v := by
      rw [coeff_derivative]; push_cast; ring
    have hDgt0 : coeff 0 ((d⁄dX K) gt) = coeff 1 gt := by
      rw [coeff_derivative]; push_cast; ring
    have h1 := congrArg (fun x : PowerSeries K => coeff 1 x) hR
    simp only [map_add, map_sub, map_smul, smul_eq_mul, coeff_one_mul_eq, coeff_zero_mul_eq,
      coeff_zero_X_eq, coeff_one_X_eq, hDv0, hDgt0, zero_mul, one_mul] at h1
    rw [hlam] at h1
    have hkey : coeff 0 gt * coeff 1 v = 0 := by linear_combination h1
    exact (mul_eq_zero.mp hkey).resolve_left hgt0
  have : coeff 3 e₂ = coeff 1 v := by
    rw [hv]
    simpa using PowerSeries.coeff_X_pow_mul v 2 1
  rw [this, hv1]

/-! ## Rank one: the tensor normal form -/

theorem vfTensorDefect_one_eq_deriv (f η : PowerSeries K) :
    vfTensorDefect 1 f η = (d⁄dX K) (f * η) := by
  unfold vfTensorDefect
  rw [vfDeriv_mul, one_smul]
  ring

/-- **The invariant differential of a one-dimensional transitive algebra.**  The line `K e₀` with
`e₀` a unit preserves the weight-one differential `e₀⁻¹`. -/
theorem exists_tensor_of_line {e₀ : PowerSeries K} (he₀ : coeff 0 e₀ ≠ 0) :
    ∃ η : PowerSeries K, coeff 0 η ≠ 0 ∧ ∀ a : K, vfTensorDefect 1 (a • e₀) η = 0 := by
  have hunit : constantCoeff e₀ ≠ (0 : K) := by rwa [← coeff_zero_eq_constantCoeff_apply]
  have hinv : e₀ * e₀⁻¹ = 1 := PowerSeries.mul_inv_cancel e₀ hunit
  refine ⟨e₀⁻¹, ?_, ?_⟩
  · intro hzero
    have : coeff 0 (e₀ * e₀⁻¹) = 0 := by rw [coeff_zero_mul_eq, hzero, mul_zero]
    rw [hinv] at this
    simp at this
  · intro a
    rw [vfTensorDefect_one_eq_deriv, smul_mul_assoc, hinv, Derivation.map_smul,
      Derivation.map_one_eq_zero, smul_zero]

/-! ## From an affine to a projective connection -/

theorem vfRho_zero (f : PowerSeries K) : vfRho f 0 = 0 := by
  unfold vfRho
  simp

theorem vfProjDefect_eq_zero_of_affine {f μ : PowerSeries K} (h : vfAffineDefect f μ = 0) :
    vfProjDefect f (2 * (d⁄dX K) μ - μ * μ) = 0 := by
  rw [vfProjDefect_projectivization, h]
  simp

/-! ## The projective connection of a rank-three algebra -/

theorem vfDeriv_X_cube : (d⁄dX K) ((X : PowerSeries K) ^ 3) = 3 * X ^ 2 := by
  have h : ((X : PowerSeries K) ^ 3) = X * (X * X) := by ring
  rw [h, vfDeriv_mul, vfDeriv_mul]
  simp
  ring

/-- **The projective normal form.**  A transitive finite-dimensional bracket-closed algebra of
formal vector fields containing a field of order two preserves a projective connection.

The connection is the quotient `q = ((e₂′)² − 2 e₂ e₂″)/e₂²`, which is regular precisely because
bracket-closedness forces `coeff 3 e₂ = 0`.  That `e₂` preserves `q` is the identity
`((f′)² − 2 f f″)′ = −2 f f‴`; that the whole algebra does then follows from the cocycle identity,
because `ρ(e₂) w = 0` forces `w = 0`. -/
theorem exists_projConnection_of_hasOrder_two [CharZero K]
    {L : Submodule K (PowerSeries K)} [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {e₀ e₂ : PowerSeries K} (he₀L : e₀ ∈ L) (he₀ : HasOrder e₀ 0)
    (he₂L : e₂ ∈ L) (he₂ : HasOrder e₂ 2) :
    ∃ q : PowerSeries K, ∀ f ∈ L, vfProjDefect f q = 0 := by
  classical
  have he₂ne : e₂ ≠ 0 := he₂.ne_zero
  have hsep : ∀ h ∈ L, coeff 0 h = 0 → coeff 1 h = 0 → coeff 2 h = 0 → h = 0 := by
    intro h hhL h0 h1 h2
    by_contra hne
    obtain ⟨n, hn⟩ := exists_hasOrder_of_ne_zero hne
    have hle : n ≤ 2 := hasOrder_le_two_of_finiteDimensional hL he₀L he₀ hhL hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact hn.1 h0
    · exact hn.1 h1
    · exact hn.1 h2
  set g : PowerSeries K := vfBracket e₂ e₀ with hgdef
  have hgL : g ∈ L := hL e₂ he₂L e₀ he₀L
  have hg : HasOrder g 1 := by
    have h := hasOrder_vfBracket he₂ he₀ (by norm_num : (2 : ℕ) ≠ 0)
    simpa [hgdef] using h
  have hbrL : vfBracket g e₂ ∈ L := hL g hgL e₂ he₂L
  have hbrO : HasOrder (vfBracket g e₂) 2 := by
    have h := hasOrder_vfBracket hg he₂ (by norm_num : (1 : ℕ) ≠ 2)
    simpa using h
  set lam : K := coeff 2 (vfBracket g e₂) / coeff 2 e₂ with hlamdef
  have hrel : vfBracket g e₂ = lam • e₂ := by
    have hmem : vfBracket g e₂ - lam • e₂ ∈ L :=
      Submodule.sub_mem L hbrL (Submodule.smul_mem L lam he₂L)
    have h0 : coeff 0 (vfBracket g e₂ - lam • e₂) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hbrO.2 0 (by norm_num),
        he₂.2 0 (by norm_num)]
      ring
    have h1 : coeff 1 (vfBracket g e₂ - lam • e₂) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hbrO.2 1 (by norm_num),
        he₂.2 1 (by norm_num)]
      ring
    have h2 : coeff 2 (vfBracket g e₂ - lam • e₂) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hlamdef,
        div_mul_cancel₀ (coeff 2 (vfBracket g e₂)) he₂.1]
      ring
    exact sub_eq_zero.mp (hsep _ hmem h0 h1 h2)
  have hc3 : coeff 3 e₂ = 0 := coeff_three_eq_zero_of_bracket hg he₂ hrel
  -- the factorization `e₂ = X² v` with `v` a unit and `v′ = X w`
  obtain ⟨v, hv⟩ : (X : PowerSeries K) ^ 2 ∣ e₂ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    exact he₂.2 m hm
  have hv0 : coeff 0 v ≠ 0 := by
    have h : coeff 2 e₂ = coeff 0 v := by
      rw [hv]; simpa using PowerSeries.coeff_X_pow_mul v 2 0
    rw [← h]; exact he₂.1
  have hv1 : coeff 1 v = 0 := by
    have h : coeff 3 e₂ = coeff 1 v := by
      rw [hv]; simpa using PowerSeries.coeff_X_pow_mul v 2 1
    rw [← h, hc3]
  obtain ⟨w, hw⟩ : (X : PowerSeries K) ∣ (d⁄dX K) v := by
    rw [PowerSeries.X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply, coeff_derivative, hv1]
    ring
  -- the derivatives of `e₂`, written in the factorization
  have hDe₂ : (d⁄dX K) e₂ = X ^ 3 * w + 2 * (X * v) := by
    rw [hv, vfDeriv_mul, vfDeriv_X_sq, hw]
    ring
  have hD2e₂ : (d⁄dX K) ((d⁄dX K) e₂) = X ^ 3 * (d⁄dX K) w + 5 * (X ^ 2 * w) + 2 * v := by
    rw [hDe₂]
    simp only [map_add, vfDeriv_mul, vfDeriv_X_cube, vfDeriv_two,
      PowerSeries.derivative_X, mul_zero, add_zero, hw]
    ring
  set G : PowerSeries K := X ^ 2 * (w * w) - 6 * (v * w) - 2 * (X * (v * (d⁄dX K) w)) with hGdef
  have hQG : (d⁄dX K) e₂ * (d⁄dX K) e₂ - 2 * (e₂ * (d⁄dX K) ((d⁄dX K) e₂)) = X ^ 4 * G := by
    rw [hD2e₂, hDe₂, hv, hGdef]
    ring
  have hvvunit : constantCoeff (v * v) ≠ (0 : K) := by
    rw [map_mul, ← coeff_zero_eq_constantCoeff_apply]
    exact mul_ne_zero hv0 hv0
  have hvvinv : (v * v) * (v * v)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hvvunit
  set q : PowerSeries K := G * (v * v)⁻¹ with hqdef
  have hq : q * (e₂ * e₂)
      = (d⁄dX K) e₂ * (d⁄dX K) e₂ - 2 * (e₂ * (d⁄dX K) ((d⁄dX K) e₂)) := by
    rw [hQG, hqdef, hv]
    have h : G * (v * v)⁻¹ * (X ^ 2 * v * (X ^ 2 * v)) = X ^ 4 * G * ((v * v) * (v * v)⁻¹) := by
      ring
    rw [h, hvvinv, mul_one]
  have hpd₂ : vfProjDefect e₂ q = 0 := vfProjDefect_eq_zero_of_quotient he₂ne hq
  have hrho : ∀ B : PowerSeries K, vfRho e₂ B = 0 → B = 0 := fun B hB =>
    eq_zero_of_vfRho_eq_zero he₂ne (he₂.2 0 (by norm_num)) hB
  have hPg : vfProjDefect g q = 0 := by
    have hcoc := vfProjDefect_vfBracket g e₂ q
    rw [hrel, vfProjDefect_smul, hpd₂, smul_zero, vfRho_zero, zero_sub] at hcoc
    exact hrho _ (neg_eq_zero.mp hcoc.symm)
  have hPe₀ : vfProjDefect e₀ q = 0 := by
    have hcoc := vfProjDefect_vfBracket e₂ e₀ q
    rw [← hgdef, hPg, hpd₂, vfRho_zero, sub_zero] at hcoc
    exact hrho _ hcoc.symm
  refine ⟨q, ?_⟩
  intro f hfL
  -- read off the three coordinates
  set a : K := coeff 0 f / coeff 0 e₀ with hadef
  have hf₁L : f - a • e₀ ∈ L := Submodule.sub_mem L hfL (Submodule.smul_mem L a he₀L)
  have h₁0 : coeff 0 (f - a • e₀) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hadef,
      div_mul_cancel₀ (coeff 0 f) he₀.1]
    ring
  set b : K := coeff 1 (f - a • e₀) / coeff 1 g with hbdef
  have hf₂L : f - a • e₀ - b • g ∈ L := Submodule.sub_mem L hf₁L (Submodule.smul_mem L b hgL)
  have h₂0 : coeff 0 (f - a • e₀ - b • g) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, h₁0, hg.2 0 (by norm_num)]
    ring
  have h₂1 : coeff 1 (f - a • e₀ - b • g) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, hbdef, div_mul_cancel₀ _ hg.1, sub_self]
  set c : K := coeff 2 (f - a • e₀ - b • g) / coeff 2 e₂ with hcdef
  have hf₃L : f - a • e₀ - b • g - c • e₂ ∈ L :=
    Submodule.sub_mem L hf₂L (Submodule.smul_mem L c he₂L)
  have h₃0 : coeff 0 (f - a • e₀ - b • g - c • e₂) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, h₂0, he₂.2 0 (by norm_num)]
    ring
  have h₃1 : coeff 1 (f - a • e₀ - b • g - c • e₂) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, h₂1, he₂.2 1 (by norm_num)]
    ring
  have h₃2 : coeff 2 (f - a • e₀ - b • g - c • e₂) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, hcdef, div_mul_cancel₀ _ he₂.1, sub_self]
  have hzero := hsep _ hf₃L h₃0 h₃1 h₃2
  have hfeq : f = a • e₀ + b • g + c • e₂ := by
    have := sub_eq_zero.mp (by linear_combination hzero :
      f - (a • e₀ + b • g + c • e₂) = 0)
    exact this
  rw [hfeq, vfProjDefect_add, vfProjDefect_add, vfProjDefect_smul, vfProjDefect_smul,
    vfProjDefect_smul, hPe₀, hPg, hpd₂]
  simp

/-! ## The trichotomy -/

/-- **The affine normal form.**  A transitive finite-dimensional bracket-closed algebra with no
field of order two preserves an affine connection.  Its structure constants are read off from the
single bracket `[e₀, e₁]`, and the connection is `(−β − e₀′)/e₀`. -/
theorem exists_affineConnection_of_no_order_two [CharZero K]
    {L : Submodule K (PowerSeries K)} [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {e₀ : PowerSeries K} (he₀L : e₀ ∈ L) (he₀ : HasOrder e₀ 0)
    (hno : ¬ ∃ w ∈ L, HasOrder w 2) :
    ∃ μ : PowerSeries K, ∀ f ∈ L, vfAffineDefect f μ = 0 := by
  classical
  by_cases hone : ∃ w ∈ L, HasOrder w 1
  · obtain ⟨e₁, he₁L, he₁⟩ := hone
    have hsep : ∀ h ∈ L, coeff 0 h = 0 → coeff 1 h = 0 → h = 0 := by
      intro h hhL h0 h1
      by_contra hne
      obtain ⟨n, hn⟩ := exists_hasOrder_of_ne_zero hne
      have hle : n ≤ 2 := hasOrder_le_two_of_finiteDimensional hL he₀L he₀ hhL hn
      have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact hn.1 h0
      · exact hn.1 h1
      · exact hno ⟨h, hhL, hn⟩
    have hdec : ∀ f ∈ L, ∃ a b : K, f = a • e₀ + b • e₁ := by
      intro f hfL
      refine ⟨coeff 0 f / coeff 0 e₀,
        coeff 1 (f - (coeff 0 f / coeff 0 e₀) • e₀) / coeff 1 e₁, ?_⟩
      set a : K := coeff 0 f / coeff 0 e₀ with hadef
      set b : K := coeff 1 (f - a • e₀) / coeff 1 e₁ with hbdef
      have hmem : f - a • e₀ - b • e₁ ∈ L :=
        Submodule.sub_mem L (Submodule.sub_mem L hfL (Submodule.smul_mem L a he₀L))
          (Submodule.smul_mem L b he₁L)
      have h0 : coeff 0 (f - a • e₀ - b • e₁) = 0 := by
        rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hadef,
          div_mul_cancel₀ _ he₀.1, he₁.2 0 (by norm_num), mul_zero, sub_zero, sub_self]
      have h1 : coeff 1 (f - a • e₀ - b • e₁) = 0 := by
        rw [map_sub, map_smul, smul_eq_mul, hbdef, div_mul_cancel₀ _ he₁.1, sub_self]
      have hz := hsep _ hmem h0 h1
      exact sub_eq_zero.mp (by linear_combination hz : f - (a • e₀ + b • e₁) = 0)
    obtain ⟨α, β, hbr⟩ := hdec _ (hL e₀ he₀L e₁ he₁L)
    obtain ⟨μ, hμ0, hμ1⟩ := exists_affineConnection_of_pair he₀.1 hbr
    refine ⟨μ, ?_⟩
    intro f hfL
    obtain ⟨a, b, rfl⟩ := hdec f hfL
    rw [vfAffineDefect_add, vfAffineDefect_smul, vfAffineDefect_smul, hμ0, hμ1]
    simp
  · have hsep1 : ∀ h ∈ L, coeff 0 h = 0 → h = 0 := by
      intro h hhL h0
      by_contra hne
      obtain ⟨n, hn⟩ := exists_hasOrder_of_ne_zero hne
      have hle : n ≤ 2 := hasOrder_le_two_of_finiteDimensional hL he₀L he₀ hhL hn
      have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact hn.1 h0
      · exact hone ⟨h, hhL, hn⟩
      · exact hno ⟨h, hhL, hn⟩
    have hdec : ∀ f ∈ L, ∃ a : K, f = a • e₀ := by
      intro f hfL
      refine ⟨coeff 0 f / coeff 0 e₀, ?_⟩
      set a : K := coeff 0 f / coeff 0 e₀ with hadef
      have hmem : f - a • e₀ ∈ L := Submodule.sub_mem L hfL (Submodule.smul_mem L a he₀L)
      have h0 : coeff 0 (f - a • e₀) = 0 := by
        rw [map_sub, map_smul, smul_eq_mul, hadef, div_mul_cancel₀ _ he₀.1, sub_self]
      exact sub_eq_zero.mp (hsep1 _ hmem h0)
    have hbr : vfBracket e₀ (0 : PowerSeries K) = (0 : K) • e₀ + (0 : K) • (0 : PowerSeries K) := by
      simp [vfBracket]
    obtain ⟨μ, hμ0, _⟩ := exists_affineConnection_of_pair he₀.1 hbr
    refine ⟨μ, ?_⟩
    intro f hfL
    obtain ⟨a, rfl⟩ := hdec f hfL
    rw [vfAffineDefect_smul, hμ0, smul_zero]

/-- **The tensor normal form.**  If the only realized order is zero, the algebra is the line
`K e₀` and it preserves the weight-one differential `e₀⁻¹`. -/
theorem exists_tensorConnection_of_order_zero [CharZero K]
    {L : Submodule K (PowerSeries K)} [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {e₀ : PowerSeries K} (he₀L : e₀ ∈ L) (he₀ : HasOrder e₀ 0)
    (hno1 : ¬ ∃ w ∈ L, HasOrder w 1) (hno2 : ¬ ∃ w ∈ L, HasOrder w 2) :
    ∃ η : PowerSeries K, coeff 0 η ≠ 0 ∧ ∀ f ∈ L, vfTensorDefect 1 f η = 0 := by
  classical
  have hsep1 : ∀ h ∈ L, coeff 0 h = 0 → h = 0 := by
    intro h hhL h0
    by_contra hne
    obtain ⟨n, hn⟩ := exists_hasOrder_of_ne_zero hne
    have hle : n ≤ 2 := hasOrder_le_two_of_finiteDimensional hL he₀L he₀ hhL hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact hn.1 h0
    · exact hno1 ⟨h, hhL, hn⟩
    · exact hno2 ⟨h, hhL, hn⟩
  obtain ⟨η, hη, hηzero⟩ := exists_tensor_of_line he₀.1
  refine ⟨η, hη, ?_⟩
  intro f hfL
  have hmem : f - (coeff 0 f / coeff 0 e₀) • e₀ ∈ L :=
    Submodule.sub_mem L hfL (Submodule.smul_mem L _ he₀L)
  have h0 : coeff 0 (f - (coeff 0 f / coeff 0 e₀) • e₀) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ he₀.1, sub_self]
  have hfeq : f = (coeff 0 f / coeff 0 e₀) • e₀ := sub_eq_zero.mp (hsep1 _ hmem h0)
  rw [hfeq]
  exact hηzero _

/-- **Every transitive finite-dimensional algebra of formal vector fields on a line preserves a
projective connection.**  This is the normal-form half of the Lie--Cartan trichotomy: rank one
gives a tensor, rank two an affine connection, rank three a projective connection, and the first
two structures projectivize to the third. -/
theorem exists_projConnection [CharZero K] {L : Submodule K (PowerSeries K)}
    [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {e₀ : PowerSeries K} (he₀L : e₀ ∈ L) (he₀ : HasOrder e₀ 0) :
    ∃ q : PowerSeries K, ∀ f ∈ L, vfProjDefect f q = 0 := by
  by_cases h : ∃ w ∈ L, HasOrder w 2
  · obtain ⟨w, hwL, hw⟩ := h
    exact exists_projConnection_of_hasOrder_two hL he₀L he₀ hwL hw
  · obtain ⟨μ, hμ⟩ := exists_affineConnection_of_no_order_two hL he₀L he₀ h
    exact ⟨2 * (d⁄dX K) μ - μ * μ, fun f hf => vfProjDefect_eq_zero_of_affine (hμ f hf)⟩

/-- **The trichotomy, assembled.**  A transitive finite-dimensional bracket-closed algebra of
formal vector fields on a line is the infinitesimal symmetry algebra of a weight-one differential,
of an affine connection, or of a projective connection, according to which orders it realizes —
and in every case of a projective connection. -/
theorem lieCartan_normal_form_trichotomy [CharZero K] {L : Submodule K (PowerSeries K)}
    [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {e₀ : PowerSeries K} (he₀L : e₀ ∈ L) (he₀ : HasOrder e₀ 0) :
    ((¬ ∃ w ∈ L, HasOrder w 1) → (¬ ∃ w ∈ L, HasOrder w 2) →
        ∃ η : PowerSeries K, coeff 0 η ≠ 0 ∧ ∀ f ∈ L, vfTensorDefect 1 f η = 0) ∧
      ((¬ ∃ w ∈ L, HasOrder w 2) → ∃ μ : PowerSeries K, ∀ f ∈ L, vfAffineDefect f μ = 0) ∧
      (∃ q : PowerSeries K, ∀ f ∈ L, vfProjDefect f q = 0) :=
  ⟨fun h1 h2 => exists_tensorConnection_of_order_zero hL he₀L he₀ h1 h2,
    fun h2 => exists_affineConnection_of_no_order_two hL he₀L he₀ h2,
    exists_projConnection hL he₀L he₀⟩

end GaloisForLFunctions.HTGeometry

end
