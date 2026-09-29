import GaloisForLFunctions.HTGeometry.ConnectionBellPolynomials

/-!
# The shift symmetry of a collapse of the affine logarithmic tower

In a Ritt frame let `u` solve the affine transport equation `σ u = ρ⁻¹u + b` of an affine connection
and `v` the eigen-equation `σ v = ρ⁻¹v`, with `d v = u·v` (`u` is the connection of the coordinate
`∫ v`).  Then `u + v` solves the same affine equation: it is the connection of another invariant
coordinate.

Suppose the jets `u, du, …, d^{n−1}u` are algebraically independent and collapse,
`d^n u = F(u, …, d^{n−1}u)`.  The defect `E = d^n(u+v) − F(u+v, …)` of the second connection is a
`ρ^{−(n+1)}`-eigenvector, so `E = k·v^{n+1}` with `k` in the base.

The jets of `v` are `v·B_j(u)` for the Bell polynomials `B_j`, so the jets of `u + v` are the line
substitution `x_j ↦ x_j + s·B_j(x)` at `s = v`.  When `v` is moreover transcendental over the jets
of
`u`, the defect identity is a polynomial identity:

`F(x + s·B(x)) = F(x) + s·B_n(x) − k·s^{n+1}`.

The line substitution commutes with the weight scalings, so `F(λ·x) − λ^{n+1}F(x)` is constant along
the lines, hence constant: **every non-constant monomial of `F` has weight exactly `n + 1`.**
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

/-! ### The defect of the shifted connection -/

theorem sigma_add_eigen {u v : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) :
    Fr.σ (u + v) = algebraMap K L Fr.ρ⁻¹ * (u + v) + algebraMap K L b := by
  rw [map_add, hu, hv]
  ring

/-- **The shifted connection has an eigen-defect.** -/
theorem exists_shift_defect {u v : L} {b : K} {n : ℕ}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n)) {F : MvPolynomial (Fin n) K}
    (hcol : Fr.d^[n] u = aeval (Fr.jetFamily u n) F) :
    ∃ k : K, Fr.ψ k = k ∧
      Fr.d^[n] (u + v) - aeval (Fr.jetFamily (u + v) n) F = algebraMap K L k * v ^ (n + 1) := by
  have hρ : algebraMap K L Fr.ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr Fr.ρ_ne
  -- the collapse as a polynomial identity
  have hrel : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ * aeval (Fr.jetFamily u n) F
        + aeval (Fr.jetFamily u n) (Fr.defectPoly b n) := by
    rw [← hcol, Fr.sigma_jet_eq_defect hu n, aeval_defectPoly]
  have hpoly := Fr.towerShift_eq_of_collapse hu hind hrel
  -- the same identity at the shifted connection
  set x := u + v with hxdef
  have hx := Fr.sigma_add_eigen hu hv
  have hFx : Fr.σ (aeval (Fr.jetFamily x n) F)
      = algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ * aeval (Fr.jetFamily x n) F + Fr.towerDefect x b n := by
    have h := Fr.aeval_towerShift hx n F
    rw [hpoly] at h
    have hj : (fun j : Fin n => Fr.d^[(j : ℕ)] x) = Fr.jetFamily x n := rfl
    rw [hj, map_add, map_mul, aeval_C, aeval_defectPoly] at h
    exact h.symm
  set E := Fr.d^[n] x - aeval (Fr.jetFamily x n) F with hE
  have hσE : Fr.σ E = algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ * E := by
    rw [hE, map_sub, Fr.sigma_jet_eq_defect hx n, hFx]
    ring
  -- divide by the eigenvector `v^{n+1}`
  have hvpow : v ^ (n + 1) ≠ 0 := pow_ne_zero _ hv0
  have hσv : Fr.σ (v ^ (n + 1)) = algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ * v ^ (n + 1) := by
    rw [map_pow, hv, mul_pow, ← map_pow, inv_pow]
  have hfix : Fr.σ (E / v ^ (n + 1)) = E / v ^ (n + 1) := by
    have hc : algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr (inv_ne_zero (pow_ne_zero _ Fr.ρ_ne))
    rw [map_div₀, hσE, hσv, mul_div_mul_left _ _ hc]
  obtain ⟨k, hk⟩ := Fr.fixed _ hfix
  refine ⟨k, ?_, ?_⟩
  · apply (algebraMap K L).injective
    rw [← Fr.comp, hk, hfix]
  · rw [hk, div_mul_cancel₀ _ hvpow]

/-! ### The line identity -/

/-- The Bell field `x_j ↦ B_j(x)`. -/
def bellField (K : Type*) [Field K] (n : ℕ) : Fin n → MvPolynomial (Fin n) K :=
  fun j => connBell K n j

/-- **The line identity.**  If `d v = u·v` and `v` is algebraically independent of the jets of `u`,
the collapsing polynomial satisfies `F(x + s·B(x)) = F(x) + s·B_n(x) − k·s^{n+1}`. -/
theorem triLineSubst_collapse {u v : L} {b : K} {n : ℕ}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    (hind' : AlgebraicIndependent K (Fin.cons v (Fr.jetFamily u n) : Fin (n + 1) → L))
    {F : MvPolynomial (Fin n) K} (hcol : Fr.d^[n] u = aeval (Fr.jetFamily u n) F) :
    ∃ k : K, Fr.ψ k = k ∧
      aeval (triLineSubst (bellField K n)) F
        = rename Fin.succ F + X 0 * rename Fin.succ (connBell K n n) - C k * X 0 ^ (n + 1) := by
  obtain ⟨k, hψk, hk⟩ := Fr.exists_shift_defect hu hv hv0 hind hcol
  refine ⟨k, hψk, hind' ?_⟩
  set w : Fin (n + 1) → L := Fin.cons v (Fr.jetFamily u n) with hw
  have hwsucc : w ∘ Fin.succ = Fr.jetFamily u n := by
    funext j
    simp [hw]
  have hline : ∀ j : Fin n, aeval w (triLineSubst (bellField K n) j) = Fr.d^[(j : ℕ)] (u + v) := by
    intro j
    rw [triLineSubst, map_add, map_mul, aeval_X, aeval_X, aeval_rename, hwsucc, Fr.iterate_d_add,
      Fr.iterate_d_eq_mul_connBell hdv n j j.isLt.le]
    simp [hw, bellField, jetFamily]
  have hcomp : aeval w (aeval (triLineSubst (bellField K n)) F)
      = aeval (Fr.jetFamily (u + v) n) F := by
    have h := MvPolynomial.comp_aeval (triLineSubst (bellField K n))
      (aeval w : MvPolynomial (Fin (n + 1)) K →ₐ[K] L)
    have := congrArg (fun f => f F) h
    simp only [AlgHom.comp_apply] at this
    rw [this, show (fun i => (aeval w) (triLineSubst (bellField K n) i)) = Fr.jetFamily (u + v) n
      from funext hline]
  rw [hcomp, map_sub, map_add, map_mul, map_mul, aeval_X, aeval_rename, aeval_rename, hwsucc,
    map_pow, aeval_X, aeval_C]
  have hv' : w 0 = v := by simp [hw]
  rw [hv', ← hcol, ← Fr.iterate_d_eq_mul_connBell hdv n n le_rfl, ← Fr.iterate_d_add, ← hk]
  ring

/-! ### Weights along the lines -/

/-- The weight scaling of the two-sided ring: `s ↦ λ s`, `x_j ↦ λ^{j+1} x_j`. -/
def lineWeightScale (n : ℕ) (c : K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval fun i : Fin (n + 1) =>
    Fin.cases (C c * X 0) (fun j : Fin n => C (c ^ ((j : ℕ) + 1)) * X j.succ) i

theorem lineWeightScale_rename (n : ℕ) (c : K) (P : MvPolynomial (Fin n) K) :
    lineWeightScale n c (rename Fin.succ P) = rename Fin.succ (jetWeightScale n c P) := by
  have h : (lineWeightScale n c).comp (rename Fin.succ)
      = (rename Fin.succ).comp (jetWeightScale n c) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [lineWeightScale, jetWeightScale]
  exact congrArg (fun f => f P) h

theorem lineWeightScale_X_zero (n : ℕ) (c : K) :
    lineWeightScale n c (X 0) = C c * X 0 := by
  simp [lineWeightScale]

/-- **The line substitution commutes with the weight scalings.** -/
theorem aeval_lineSubst_jetWeightScale (n : ℕ) (c : K) (P : MvPolynomial (Fin n) K) :
    aeval (triLineSubst (bellField K n)) (jetWeightScale n c P)
      = lineWeightScale n c (aeval (triLineSubst (bellField K n)) P) := by
  have h : (aeval (triLineSubst (bellField K n))).comp (jetWeightScale n c)
      = (lineWeightScale n c).comp (aeval (triLineSubst (bellField K n))) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [AlgHom.comp_apply, aeval_X]
    rw [jetWeightScale_X, map_mul, aeval_C, aeval_X, triLineSubst, map_add, map_mul,
      lineWeightScale_X_zero, lineWeightScale_rename, bellField, jetWeightScale_connBell]
    simp only [lineWeightScale, aeval_X, Fin.cases_succ, algebraMap_eq, map_mul, rename_C]
    rw [pow_succ]
    simp only [map_mul, map_pow]
    ring
  exact congrArg (fun f => f P) h

theorem two_pow_injective_of_charZero [CharZero K] {a b : ℕ} (h : (2 : K) ^ a = 2 ^ b) :
    a = b := by
  have h' : ((2 ^ a : ℕ) : K) = ((2 ^ b : ℕ) : K) := by push_cast; exact h
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective h')

/-- **The weight structure of a collapse with an independent eigen-coordinate.**  Every
non-constant monomial of the collapsing polynomial has weight `n + 1`. -/
theorem coeff_eq_zero_of_lineSubst_collapse [CharZero K] {n : ℕ} {F : MvPolynomial (Fin n) K}
    {k : K}
    (hF : aeval (triLineSubst (bellField K n)) F
        = rename Fin.succ F + X 0 * rename Fin.succ (connBell K n n) - C k * X 0 ^ (n + 1))
    {e : Fin n →₀ ℕ} (he : e ≠ 0) (hw : Finsupp.weight (jetWeight n) e ≠ n + 1) :
    coeff e F = 0 := by
  set G := jetWeightScale n (2 : K) F - C ((2 : K) ^ (n + 1)) * F with hG
  have hinv : aeval (triLineSubst (bellField K n)) G = rename Fin.succ G := by
    have hC : lineWeightScale n (2 : K) (C k) = C k := by simp [lineWeightScale]
    rw [hG, map_sub, aeval_lineSubst_jetWeightScale, map_mul, aeval_C, hF]
    simp only [map_sub, map_add, map_mul, map_pow, lineWeightScale_X_zero, lineWeightScale_rename,
      jetWeightScale_connBell, rename_C, algebraMap_eq, hC]
    ring
  have hconst := eq_C_of_lineSubst_invariant (isUnitriangularField_connBell K n) hinv
  have hce := congrArg (coeff e) hconst
  rw [coeff_C, if_neg (Ne.symm he), hG, coeff_sub, coeff_jetWeightScale, coeff_C_mul] at hce
  have h2 : (2 : K) ^ (Finsupp.weight (jetWeight n) e) - 2 ^ (n + 1) ≠ 0 := by
    intro h
    exact hw (two_pow_injective_of_charZero (sub_eq_zero.mp h))
  have : ((2 : K) ^ (Finsupp.weight (jetWeight n) e) - 2 ^ (n + 1)) * coeff e F = 0 := by
    rw [sub_mul]
    exact hce
  exact (mul_eq_zero.mp this).resolve_left h2

end RittFrame

end

end GaloisForLFunctions.HTGeometry
