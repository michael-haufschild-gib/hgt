import GaloisForLFunctions.RHTower.EstermannEntire
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The principal part of Estermann's zeta function at `s = 1`

For `a` a unit mod `q` the character sum in the polar decomposition collapses completely:
summing `expZeta` over a full residue system is a discrete Fourier transform of the constant
function, so

```text
∑_{c mod q} expZeta(ac/q, s) = q^{1-s} ζ(s),      estermannCharSum q a s = (q^{1-s} - 1) ζ(s).
```

Substituting this into the polar decomposition removes the character sum entirely:

```text
D(s, a/q) = q^{1-2s} ζ(s)² + q^{-s} R_a(s),
```

with `R_a` entire.  The two `ζ` factors carry the whole pole, so the entire completion is
`q^{1-2s} ζ₁(s)² + q^{-s}(s-1)² R_a(s)`, and its value and derivative at `s = 1` are the
double-pole coefficient and the residue of `D`:

```text
D(s, a/q) = (1/q) (s-1)^{-2} + ((2γ - 2 log q)/q) (s-1)^{-1} + O(1).
```

Both are independent of `a`.
-/

open Complex HurwitzZeta

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The discrete Fourier transform of the constant function `1` on `ZMod q` is `q` times the
indicator of `0`.  Proved by Fourier inversion applied to the indicator. -/
theorem dft_const_one (q : ℕ) [NeZero q] :
    ZMod.dft (fun _ : ZMod q => (1 : ℂ)) = fun k => if k = 0 then (q : ℂ) else 0 := by
  have hΨ : ZMod.dft (fun k : ZMod q => if k = 0 then (1 : ℂ) else 0) = fun _ => (1 : ℂ) := by
    funext k
    rw [ZMod.dft_apply, Finset.sum_eq_single (0 : ZMod q)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hd := ZMod.dft_dft (fun k : ZMod q => if k = 0 then (1 : ℂ) else 0)
  rw [hΨ] at hd
  rw [hd]
  funext j
  by_cases h : j = 0 <;> simp [h]

/-- **The full residue sum of `expZeta` is `q^{1-s} ζ(s)`.** -/
theorem sum_expZeta_eq (q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    ∑ c : ZMod q, expZeta (ZMod.toAddCircle c) s = (q : ℂ) ^ (1 - s) * riemannZeta s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have h := ZMod.LFunction_dft (N := q) (fun _ : ZMod q => (1 : ℂ)) (Or.inr hs)
  rw [dft_const_one] at h
  have hL : ZMod.LFunction (fun k : ZMod q => if k = 0 then (q : ℂ) else 0) s
      = (q : ℂ) ^ (1 - s) * riemannZeta s := by
    rw [ZMod.LFunction, Finset.sum_eq_single (0 : ZMod q)]
    · rw [if_pos rfl, map_zero, hurwitzZeta_zero, ← mul_assoc]
      congr 1
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hq0, Complex.cpow_one, mul_comm]
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL] at h
  rw [h]
  exact Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun c => by simp)

/-- **The Estermann character sum has a closed form.**  For `a` a unit the sum over nonzero
residues is `(q^{1-s} - 1) ζ(s)`. -/
theorem estermannCharSum_eq (a : (ZMod q)ˣ) {s : ℂ} (hs : s ≠ 1) :
    estermannCharSum q ((a : ZMod q)) s = ((q : ℂ) ^ (1 - s) - 1) * riemannZeta s := by
  have hfull : ∑ c : ZMod q, expZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s
      = (q : ℂ) ^ (1 - s) * riemannZeta s := by
    rw [← sum_expZeta_eq q hs]
    exact Fintype.sum_equiv (unitsMulPerm a) _ _ (fun c => by rw [unitsMulPerm_apply])
  have hsplit : ∑ c : ZMod q, expZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s
      = expZeta (ZMod.toAddCircle ((a : ZMod q) * 0)) s + estermannCharSum q ((a : ZMod q)) s := by
    rw [estermannCharSum]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))).symm
  rw [hsplit, mul_zero, map_zero, expZeta_zero] at hfull
  rw [sub_mul, one_mul, ← hfull]
  ring

/-- **The character sum disappears from the polar decomposition.** -/
theorem estermannZeta_eq_zetaSq_add (a : (ZMod q)ˣ) {s : ℂ} (hs : s ≠ 1) :
    estermannZeta q ((a : ZMod q)) s
      = (q : ℂ) ^ (1 - 2 * s) * riemannZeta s ^ (2 : ℕ)
        + (q : ℂ) ^ (-s) * estermannRegularPart q ((a : ZMod q)) s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hcp : (q : ℂ) ^ (-s) * (q : ℂ) ^ (1 - s) = (q : ℂ) ^ (1 - 2 * s) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    ring
  rw [estermannZeta_eq_polar_add_regular, estermannCharSum_eq a hs,
    show (riemannZeta s + ((q : ℂ) ^ (1 - s) - 1) * riemannZeta s) * riemannZeta s
      = (q : ℂ) ^ (1 - s) * riemannZeta s ^ (2 : ℕ) by ring,
    mul_add, ← mul_assoc, hcp]

/-- The corpus entire completion of `ζ` agrees with mathlib's `riemannZeta₁`. -/
theorem zetaEntire_eq_riemannZeta₁ : zetaEntire = riemannZeta₁ := by
  refine Continuous.ext_on (dense_compl_singleton (1 : ℂ))
    differentiable_zetaEntire.continuous differentiable_riemannZeta₁.continuous ?_
  intro s hs
  have hs' : s ≠ 1 := hs
  have hne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs'
  rw [zetaEntire_eq hs', riemannZeta₁, riemannZeta_eq_inv_sub_add hs']
  field_simp

/-- **The reduced entire completion.**  `(s-1)² D(s, a/q) = q^{1-2s} ζ₁(s)² + q^{-s}(s-1)² R_a(s)`. -/
theorem estermannEntire_eq_reduced (a : (ZMod q)ˣ) (s : ℂ) :
    estermannEntire q ((a : ZMod q)) s
      = (q : ℂ) ^ (1 - 2 * s) * riemannZeta₁ s ^ (2 : ℕ)
        + (q : ℂ) ^ (-s) * ((s - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) s) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hcont₁ : Continuous (estermannEntire q ((a : ZMod q))) :=
    (differentiable_estermannEntire a).continuous
  have hcont₂ : Continuous (fun s : ℂ => (q : ℂ) ^ (1 - 2 * s) * riemannZeta₁ s ^ (2 : ℕ)
      + (q : ℂ) ^ (-s) * ((s - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) s)) := by
    have hd : Continuous (fun z : ℂ => (q : ℂ) ^ (1 - 2 * z)) := by
      have hrw : (fun z : ℂ => (q : ℂ) ^ (1 - 2 * z))
          = fun z : ℂ => Complex.exp (Complex.log (q : ℂ) * (1 - 2 * z)) := by
        funext z; exact Complex.cpow_def_of_ne_zero hq0 _
      rw [hrw]; fun_prop
    refine Continuous.add (Continuous.mul ?_ ?_) (Continuous.mul ?_ (Continuous.mul ?_ ?_))
    · exact hd
    · exact differentiable_riemannZeta₁.continuous.pow 2
    · exact (differentiable_const_cpow_neg hq0).continuous
    · exact (continuous_id.sub continuous_const).pow 2
    · exact (differentiable_estermannRegularPart a).continuous
  refine congrFun (Continuous.ext_on (dense_compl_singleton (1 : ℂ)) hcont₁ hcont₂ ?_) s
  intro z hz
  have hz' : z ≠ 1 := hz
  have hne : z - 1 ≠ 0 := sub_ne_zero_of_ne hz'
  have hcp : (q : ℂ) ^ (-z) * (q : ℂ) ^ (1 - z) = (q : ℂ) ^ (1 - 2 * z) := by
    rw [← Complex.cpow_add _ _ hq0]; congr 1; ring
  have hz1 : (z - 1) * riemannZeta z = riemannZeta₁ z := by
    rw [riemannZeta_eq_inv_sub_mul hz', ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [estermannEntire, zetaEntire_eq_riemannZeta₁, estermannCharSum_eq a hz']
  rw [show riemannZeta₁ z ^ (2 : ℕ)
        + riemannZeta₁ z * ((z - 1) * (((q : ℂ) ^ (1 - z) - 1) * riemannZeta z))
        + (z - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) z
      = riemannZeta₁ z ^ (2 : ℕ)
        + ((q : ℂ) ^ (1 - z) - 1) * (riemannZeta₁ z * ((z - 1) * riemannZeta z))
        + (z - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) z by ring, hz1]
  rw [show riemannZeta₁ z ^ (2 : ℕ) + ((q : ℂ) ^ (1 - z) - 1) * (riemannZeta₁ z * riemannZeta₁ z)
        + (z - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) z
      = (q : ℂ) ^ (1 - z) * riemannZeta₁ z ^ (2 : ℕ)
        + (z - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) z by ring]
  rw [mul_add, ← mul_assoc, hcp]

/-- **The double-pole coefficient of `D(s, a/q)` is `1/q`.** -/
theorem estermannEntire_one (a : (ZMod q)ˣ) : estermannEntire q ((a : ZMod q)) 1 = (q : ℂ)⁻¹ := by
  rw [estermannEntire_eq_reduced]
  norm_num [Complex.cpow_neg_one]

/-- Replace the derivative value by an equal one. -/
private theorem hasDerivAt_of_eq {f : ℂ → ℂ} {u v x : ℂ} (h : HasDerivAt f u x) (huv : u = v) :
    HasDerivAt f v x := huv ▸ h

/-- **The residue of `D(s, a/q)` at `s = 1` is `(2γ - 2 log q)/q`**, independent of `a`.  It is the
derivative at `1` of the entire completion `(s-1)² D(s, a/q)`. -/
theorem hasDerivAt_estermannEntire_one (a : (ZMod q)ˣ) :
    HasDerivAt (estermannEntire q ((a : ZMod q)))
      ((q : ℂ)⁻¹ * (2 * (Real.eulerMascheroniConstant : ℂ) - 2 * Complex.log (q : ℂ))) 1 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hlin : HasDerivAt (fun s : ℂ => 1 - 2 * s) (-2) 1 :=
    hasDerivAt_of_eq (((hasDerivAt_id (1 : ℂ)).const_mul (2 : ℂ)).const_sub 1) (by norm_num)
  have hcp : HasDerivAt (fun y : ℂ => (q : ℂ) ^ y)
      ((q : ℂ) ^ (1 - 2 * (1 : ℂ)) * Complex.log (q : ℂ)) (1 - 2 * (1 : ℂ)) :=
    (hasStrictDerivAt_const_cpow (Or.inl hq0)).hasDerivAt
  have hu : HasDerivAt (fun s : ℂ => (q : ℂ) ^ (1 - 2 * s))
      ((q : ℂ) ^ (1 - 2 * (1 : ℂ)) * Complex.log (q : ℂ) * (-2)) 1 := hcp.comp 1 hlin
  have hz : HasDerivAt riemannZeta₁ (Real.eulerMascheroniConstant : ℂ) 1 := by
    have h := (differentiable_riemannZeta₁ 1).hasDerivAt
    rwa [deriv_riemannZeta₁_one] at h
  have hv : HasDerivAt (fun s : ℂ => riemannZeta₁ s ^ (2 : ℕ))
      (2 * (Real.eulerMascheroniConstant : ℂ)) 1 :=
    hasDerivAt_of_eq (hz.pow 2) (by rw [riemannZeta₁_one]; push_cast; ring)
  have hcpn : HasDerivAt (fun y : ℂ => (q : ℂ) ^ y)
      ((q : ℂ) ^ (-(1 : ℂ)) * Complex.log (q : ℂ)) (-(1 : ℂ)) :=
    (hasStrictDerivAt_const_cpow (Or.inl hq0)).hasDerivAt
  have hneg : HasDerivAt (fun s : ℂ => -s) (-1) 1 := (hasDerivAt_id (1 : ℂ)).neg
  have hq2 : HasDerivAt (fun s : ℂ => (q : ℂ) ^ (-s))
      ((q : ℂ) ^ (-(1 : ℂ)) * Complex.log (q : ℂ) * (-1)) 1 := hcpn.comp 1 hneg
  have hsq : HasDerivAt (fun s : ℂ => (s - 1) ^ (2 : ℕ)) 0 1 :=
    hasDerivAt_of_eq (((hasDerivAt_id (1 : ℂ)).sub_const 1).pow 2) (by norm_num)
  have hR : HasDerivAt (estermannRegularPart q ((a : ZMod q)))
      (deriv (estermannRegularPart q ((a : ZMod q))) 1) 1 :=
    (differentiable_estermannRegularPart a 1).hasDerivAt
  have hp : HasDerivAt
      (fun s : ℂ => (s - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) s) 0 1 :=
    hasDerivAt_of_eq (hsq.mul hR) (by norm_num)
  have hterm2 : HasDerivAt
      (fun s : ℂ => (q : ℂ) ^ (-s) * ((s - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) s))
      0 1 := hasDerivAt_of_eq (hq2.mul hp) (by norm_num)
  have hfun : estermannEntire q ((a : ZMod q))
      = fun s : ℂ => (q : ℂ) ^ (1 - 2 * s) * riemannZeta₁ s ^ (2 : ℕ)
        + (q : ℂ) ^ (-s) * ((s - 1) ^ (2 : ℕ) * estermannRegularPart q ((a : ZMod q)) s) :=
    funext (estermannEntire_eq_reduced a)
  have hone : (q : ℂ) ^ (1 - 2 * (1 : ℂ)) = (q : ℂ)⁻¹ := by
    norm_num [Complex.cpow_neg_one]
  rw [hfun]
  refine hasDerivAt_of_eq ((hu.mul hv).add hterm2) ?_
  rw [hone, riemannZeta₁_one]
  ring

/-- The residue in `deriv` form. -/
theorem deriv_estermannEntire_one (a : (ZMod q)ˣ) :
    deriv (estermannEntire q ((a : ZMod q))) 1
      = (q : ℂ)⁻¹ * (2 * (Real.eulerMascheroniConstant : ℂ) - 2 * Complex.log (q : ℂ)) :=
  (hasDerivAt_estermannEntire_one a).deriv

end

end RHTower
