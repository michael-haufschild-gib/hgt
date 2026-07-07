/-
The seam-flux cochain: the von Mangoldt weight `Λ(p^r) = log p` as the scale-flux/length quotient.

The crossing tower gives the `1/r` Euler weight as the reciprocal crossing energy `‖B_{p,r}‖²_HS = r`
(`SeamCrossingTower`).  The *arithmetic* weight `Λ(p^r) = log p` has a second, independent seam origin:
the infinitesimal logarithmic scale generator.

On the shell space (`e_n = shell |ξ|_p = p^n`) put the logarithmic position operator `X_p e_n =
n·(log p)·e_n` (`Xpos`) and the scaling shift `S_p e_n = e_{n−1}` (`Sshift`, `S_p e_n = e_{n-1}` since
`(S_p f)(n) = f(n+1)`).  The seam derivation `∇_p = −[X_p, ·]` acts on the `r`-step crossing with
eigenvalue `r·log p`:

  `[X_p, S_p^r] = −r·(log p)·S_p^r`   (`commutator_X_Spow`),

so `∇_p B_{p,r} = r·(log p)·B_{p,r}`.  Renormalizing by the crossing length `r` (the HS energy) gives
the von Mangoldt weight:

  `Λ(p^r) = log p = (r·log p)/r = (scale-flux eigenvalue)/(crossing-length eigenvalue)`
  (`vonMangoldt_eq_flux_over_length`).

So the two fundamental arithmetic coefficients have independent, intrinsic seam origins: `1/r` from
reproducing-kernel duality (crossing energy), and `Λ(p^r) = log p` from the logarithmic scale flux.
Neither is inserted; both are read off the seam operators `B_{p,r}`, `X_p`.  The flux energy
`Σ_{p,r} (log p)·‖h‖²` (`flux_energy_nonneg`) is the arithmetic-mass form, distinct from the
crossing-length form `Σ_{p,r} r·‖h‖²` (`SeamCrossingTower.finite_weil_energy_nonneg`).
-/
import GaloisForLFunctions.RHTower.SeamCrossingTower

noncomputable section

namespace RHTower

open ArithmeticFunction

/-! ### §1 The shift and the logarithmic scale generator -/

/-- The scaling shift on the shell space `ℤ → ℂ`: `(S_p f)(n) = f(n+1)`, so `S_p e_n = e_{n−1}`. -/
def Sshift : (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f := fun n => f (n + 1)
  map_add' f g := by funext n; simp
  map_smul' a f := by funext n; simp

/-- The logarithmic position operator `X_p e_n = n·c·e_n` on the shell space (`c = log p`). -/
def Xpos (c : ℂ) : (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f := fun n => (n : ℂ) * c * f n
  map_add' f g := by funext n; simp; ring
  map_smul' a f := by funext n; simp; ring

/-- The `r`-fold shift lowers the shell index by `r`: `(S_p^r f)(n) = f(n+r)`. -/
theorem shift_pow_apply (r : ℕ) (f : ℤ → ℂ) (n : ℤ) : (Sshift ^ r) f n = f (n + r) := by
  induction r generalizing f n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    show f (n + k + 1) = f (n + (k + 1 : ℕ))
    congr 1; push_cast; ring

/-! ### §2 The scale-flux commutator: the seam derivation eigenvalue -/

/-- **The seam-flux commutator.**  `[X_p, S_p^r] = −r·(log p)·S_p^r`.  Equivalently the seam
derivation `∇_p = −[X_p, ·]` scales the `r`-step crossing by `r·c`: `∇_p S_p^r = r·c·S_p^r`.  The
scale-flux eigenvalue of an `r`-crossing is `r·log p` — the numerator of the von Mangoldt weight. -/
theorem commutator_X_Spow (c : ℂ) (r : ℕ) :
    Xpos c ∘ₗ (Sshift ^ r) - (Sshift ^ r) ∘ₗ Xpos c = (-(r : ℂ) * c) • (Sshift ^ r) := by
  ext f n
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  show (n : ℂ) * c * ((Sshift ^ r) f n) - (Sshift ^ r) (fun m => (m : ℂ) * c * f m) n = _
  rw [shift_pow_apply, shift_pow_apply]
  push_cast; ring

/-- The seam derivation eigenvalue, stated directly: `∇_p S_p^r = r·c·S_p^r` where `∇_p = −[X_p, ·]`. -/
theorem seam_derivation_eigenvalue (c : ℂ) (r : ℕ) :
    (Sshift ^ r) ∘ₗ Xpos c - Xpos c ∘ₗ (Sshift ^ r) = ((r : ℂ) * c) • (Sshift ^ r) := by
  have h := commutator_X_Spow c r
  linear_combination (norm := module) -h

/-! ### §3 The von Mangoldt weight is the flux/length quotient -/

/-- **The von Mangoldt weight is the scale-flux/crossing-length quotient.**  For a prime power `p^r`
(`r ≥ 1`), the real von Mangoldt value equals `(r·log p)/r` — the scale-flux eigenvalue `r·log p`
(`commutator_X_Spow`) divided by the crossing-length eigenvalue `r` (`SeamCrossingTower.crossSupport_card`,
`‖B_{p,r}‖²_HS = r`).  The arithmetic weight is renormalized scale flux, not an inserted constant. -/
theorem vonMangoldt_eq_flux_over_length {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 0 < r) :
    vonMangoldt (p ^ r) = (r * Real.log p) / r := by
  rw [vonMangoldt_apply, if_pos ⟨p, r, hp.prime, hr, rfl⟩, Nat.Prime.pow_minFac hp hr.ne',
    mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne' : (r : ℝ) ≠ 0)]

/-- The scale-flux/length quotient is `log p`: renormalizing the flux `r·log p` by the crossing
length `r` returns the von Mangoldt weight. -/
theorem flux_over_length_eq_log (p : ℕ) {r : ℕ} (hr : 0 < r) :
    (r * Real.log p) / r = Real.log p :=
  mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne' : (r : ℝ) ≠ 0)

/-! ### §4 The flux energy is the arithmetic-mass form -/

/-- **The finite-prime flux energy is nonnegative.**  Weighting each crossing by the flux quotient
`log p` (in place of the crossing length `r`) gives `Σ_{(p,r)} (log p)·‖h‖² ≥ 0`, over primes `p ≥ 2`.
This is the arithmetic-mass energy — distinct from the crossing-length energy
`SeamCrossingTower.finite_weil_energy_nonneg` — and it is the finite-prime half of the flux-renormalized
Weil form. -/
theorem flux_energy_nonneg (S : Finset (ℕ × ℕ)) (hS : ∀ pr ∈ S, 2 ≤ pr.1) (h : ℕ × ℕ → ℂ) :
    0 ≤ ∑ pr ∈ S, Real.log pr.1 * ‖h pr‖ ^ 2 :=
  Finset.sum_nonneg fun pr hpr => by
    have hlog : 0 ≤ Real.log pr.1 :=
      Real.log_nonneg (by exact_mod_cast le_trans (by norm_num) (hS pr hpr))
    positivity

end RHTower
