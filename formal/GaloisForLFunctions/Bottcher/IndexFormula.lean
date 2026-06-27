/-
# The holomorphic fixed-point index formula for `f_c^[p]`

The connected-case dynamical core (shared by `hGtr` and the hRigid `TranscendentalOverAdjoin`) reduces,
via `ResonanceOrder.resonance_order`, to a *multiplier-spectrum* fact: a hypothetical relation pins the
multiplier `λ` of every good period-`p` point to `λ^n = 2^p` (so `‖λ‖ = 2^{p/n} ≤ 2^p`), and the genuine
open input is that this cannot hold across the whole cycle spectrum. The classical tool that constrains
the spectrum **algebraically** — flagged in the tower's status as the missing piece for a *Zdunik-free*
route — is the **holomorphic fixed-point index formula**

  `∑_{z : f_c^[p] z = z} 1/(1 - λ_z) = 0`     (sum over the `2^p` fixed points of `f_c^[p]`),

where `λ_z = (f_c^[p])'(z) = ∏_{k<p} 2·f_c^[k] z` is the multiplier. It is the residue theorem for the
rational `1`-form `dz/(z - f_c^[p] z)`: the finite fixed points carry residue `1/(1-λ_z)` and `∞`
contributes nothing (the iterate has degree `2^p ≥ 2`).

This file proves it from scratch, with no analytic input, in two layers:

* **Pure algebra** (`sum_inv_deriv_eq_zero`): for a separable `F ∈ ℂ[X]` of degree `≥ 2`,
  `∑_{r : F r = 0} 1/F'(r) = 0`. Proof: the Lagrange interpolation of the constant `1` through the `d`
  distinct roots is the polynomial `G = ∑_r F'(r)⁻¹ · (F /ₘ (X - r))`; it equals `1` (degree `≤ d-1`,
  value `1` at `d` points), so its `X^{d-1}` coefficient is `0`; that coefficient is
  `leadingCoeff F · ∑_r 1/F'(r)`. This is the residue-at-`∞`-vanishes identity, made elementary.
* **Specialisation** (`sum_index_fixedPoints_eq_zero`): apply it to `F = f_c^[p] - X`, whose roots are the
  fixed points of `f_c^[p]` and whose derivative at a root is `λ_z - 1`. Separability of `F` (no
  multiplier-`1`, i.e. parabolic, fixed point of period dividing `p`) is the one genuine side condition,
  carried as a hypothesis.

New file (hRigid / connected lane). General algebra + the quadratic-iterate polynomial layer; Mathlib only.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import GaloisForLFunctions.Bottcher.LiftPeriod

open Polynomial Finset

namespace Bottcher

/-! ### Layer 1 — the pure polynomial identity `∑ 1/F'(r) = 0` -/

variable {F : Polynomial ℂ}

/-- `F'(r) ≠ 0` at a root of a separable polynomial: a separable polynomial is coprime to its
derivative, so a common root would evaluate the Bézout identity `a·F + b·F' = 1` to `0 = 1`. -/
theorem deriv_ne_zero_of_separable (hsep : F.Separable) {r : ℂ} (hr : F.IsRoot r) :
    (derivative F).eval r ≠ 0 := by
  intro h0
  obtain ⟨a, b, hab⟩ := hsep
  have hev := congrArg (eval r) hab
  rw [eval_add, eval_mul, eval_mul, hr, h0, mul_zero, mul_zero, add_zero, eval_one] at hev
  exact zero_ne_one hev

/-- The cofactor `F /ₘ (X - r)` evaluated at a root `r` equals `F'(r)`. Writing `F = (X - r)·q`,
`F' = q + (X - r)·q'`, so `F'(r) = q(r)`. -/
theorem eval_divByMonic_eq_deriv (F : Polynomial ℂ) {r : ℂ} (hr : F.IsRoot r) :
    (F /ₘ (X - C r)).eval r = (derivative F).eval r := by
  have hfac : F = (X - C r) * (F /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hr).symm
  have hderiv : derivative F
      = (F /ₘ (X - C r)) + (X - C r) * derivative (F /ₘ (X - C r)) := by
    conv_lhs => rw [hfac]
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [hderiv, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-- **The inverse-derivative sum identity (residue theorem, algebraic form).** For a separable `F ∈ ℂ[X]`
of degree `≥ 2`, the sum of `1/F'(r)` over the distinct roots vanishes. The fixed-point index formula
rests on this. -/
theorem sum_inv_deriv_eq_zero (hsep : F.Separable) (hd : 2 ≤ F.natDegree) :
    ∑ r ∈ F.roots.toFinset, ((derivative F).eval r)⁻¹ = 0 := by
  classical
  set d := F.natDegree with hddef
  have hF0 : F ≠ 0 := by intro h; rw [hddef, h, natDegree_zero] at hd; omega
  set rs := F.roots.toFinset with hrsdef
  have hnd : F.roots.Nodup := nodup_roots hsep
  have hcard : rs.card = d := by
    rw [hrsdef, Multiset.toFinset_card_of_nodup hnd, IsAlgClosed.card_roots_eq_natDegree]
  have hroot : ∀ r ∈ rs, F.IsRoot r := by
    intro r hr; rw [hrsdef, Multiset.mem_toFinset, mem_roots hF0] at hr; exact hr
  set q : ℂ → Polynomial ℂ := fun r => F /ₘ (X - C r) with hqdef
  have hqdeg : ∀ r ∈ rs, (q r).natDegree = d - 1 := by
    intro r _; rw [hqdef, natDegree_divByMonic F (monic_X_sub_C r), natDegree_X_sub_C]
  have hqlead : ∀ r ∈ rs, (q r).leadingCoeff = F.leadingCoeff := by
    intro r hr
    have hfac : F = (X - C r) * (q r) := (mul_divByMonic_eq_iff_isRoot.mpr (hroot r hr)).symm
    have hcl := congrArg leadingCoeff hfac
    rw [leadingCoeff_mul, (monic_X_sub_C r).leadingCoeff, one_mul] at hcl
    exact hcl.symm
  have hqeval : ∀ r ∈ rs, (q r).eval r = (derivative F).eval r :=
    fun r hr => eval_divByMonic_eq_deriv F (hroot r hr)
  have hdne : ∀ r ∈ rs, (derivative F).eval r ≠ 0 :=
    fun r hr => deriv_ne_zero_of_separable hsep (hroot r hr)
  -- the Lagrange interpolation of the constant `1` through the roots
  set G : Polynomial ℂ := ∑ r ∈ rs, C (((derivative F).eval r)⁻¹) * q r with hGdef
  have hGval : ∀ s ∈ rs, G.eval s = 1 := by
    intro s hs
    rw [hGdef, eval_finsetSum, Finset.sum_eq_single s]
    · rw [eval_mul, eval_C, hqeval s hs, inv_mul_cancel₀ (hdne s hs)]
    · intro r hr hrs
      rw [eval_mul, eval_C]
      have hqrs : (q r).eval s = 0 := by
        have hfac : F = (X - C r) * (q r) := (mul_divByMonic_eq_iff_isRoot.mpr (hroot r hr)).symm
        have hFs : F.eval s = 0 := hroot s hs
        rw [hfac, eval_mul, eval_sub, eval_X, eval_C] at hFs
        rcases mul_eq_zero.mp hFs with h | h
        · exact absurd (sub_eq_zero.mp h) (fun heq => hrs (by rw [heq]))
        · exact h
      rw [hqrs, mul_zero]
    · intro hns; exact absurd hs hns
  have hGdeg : G.natDegree ≤ d - 1 := by
    rw [hGdef]
    apply natDegree_sum_le_of_forall_le
    intro r hr
    calc (C (((derivative F).eval r)⁻¹) * q r).natDegree
        ≤ (C (((derivative F).eval r)⁻¹)).natDegree + (q r).natDegree := natDegree_mul_le
      _ ≤ 0 + (d - 1) := by rw [natDegree_C]; exact add_le_add (le_refl 0) (le_of_eq (hqdeg r hr))
      _ = d - 1 := by omega
  -- a degree-`≤ d-1` polynomial equal to `1` at `d` points is `1`
  have hG1 : G = 1 := by
    by_contra hne
    set H := G - 1 with hHdef
    have hH0 : H ≠ 0 := fun h => hne (by rw [hHdef, sub_eq_zero] at h; exact h)
    have hHdeg : H.natDegree ≤ d - 1 := by
      rw [hHdef]
      calc (G - 1).natDegree ≤ max G.natDegree (1 : Polynomial ℂ).natDegree := natDegree_sub_le _ _
        _ ≤ d - 1 := by rw [natDegree_one]; exact max_le hGdeg (by omega)
    have hsub : rs ⊆ H.roots.toFinset := by
      intro r hr
      rw [Multiset.mem_toFinset, mem_roots hH0, IsRoot.def, hHdef, eval_sub, hGval r hr, eval_one,
        sub_self]
    have hcle : rs.card ≤ H.roots.toFinset.card := Finset.card_le_card hsub
    have hrle : H.roots.toFinset.card ≤ H.natDegree :=
      le_trans (Multiset.toFinset_card_le _) ((card_roots' H).trans (by simp))
    rw [hcard] at hcle
    omega
  -- compare the `X^{d-1}` coefficients of `G` and `1`
  have hcoeffG : G.coeff (d - 1) = F.leadingCoeff * ∑ r ∈ rs, ((derivative F).eval r)⁻¹ := by
    rw [hGdef, finsetSum_coeff, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [coeff_C_mul]
    have hcq : (q r).coeff (d - 1) = F.leadingCoeff := by
      rw [← hqdeg r hr, coeff_natDegree, hqlead r hr]
    rw [hcq]; ring
  have hne0 : d - 1 ≠ 0 := by omega
  have hcoeff1 : (1 : Polynomial ℂ).coeff (d - 1) = 0 := by simp [coeff_one, hne0]
  rw [hG1, hcoeff1] at hcoeffG
  exact (mul_eq_zero.mp hcoeffG.symm).resolve_left (leadingCoeff_ne_zero.mpr hF0)

/-! ### Layer 2 — the fixed-point polynomial of `f_c^[p]` and its index formula -/

/-- The polynomial `f_c^[p] - X` whose roots are the fixed points of `f_c^[p]` (= periodic points of
`f_c` of period dividing `p`). -/
noncomputable def fixedPointPoly (c : ℂ) (p : ℕ) : Polynomial ℂ := quadraticPolyIterate c p - X

theorem fixedPointPoly_eval (c : ℂ) (p : ℕ) (z : ℂ) :
    (fixedPointPoly c p).eval z = (quadratic c)^[p] z - z := by
  rw [fixedPointPoly, eval_sub, quadraticPolyIterate_eval, eval_X]

/-- `z` is a root of `f_c^[p] - X` iff it is a fixed point of `f_c^[p]`. -/
theorem fixedPointPoly_isRoot_iff (c : ℂ) (p : ℕ) (z : ℂ) :
    (fixedPointPoly c p).IsRoot z ↔ (quadratic c)^[p] z = z := by
  rw [IsRoot.def, fixedPointPoly_eval, sub_eq_zero]

/-- The fixed-point polynomial of `f_c^[p]` has degree `2^p` (for `p ≥ 1` the iterate dominates `X`). -/
theorem fixedPointPoly_natDegree (c : ℂ) {p : ℕ} (hp : 1 ≤ p) :
    (fixedPointPoly c p).natDegree = 2 ^ p := by
  rw [fixedPointPoly]
  have hdX : (X : Polynomial ℂ).natDegree < (quadraticPolyIterate c p).natDegree := by
    rw [natDegree_X, quadraticPolyIterate_natDegree]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  rw [natDegree_sub_eq_left_of_natDegree_lt hdX, quadraticPolyIterate_natDegree]

/-- **The derivative of `f_c^[p] - X` at a point is `λ_z - 1`**, where `λ_z = ∏_{k<p} 2·f_c^[k] z` is the
multiplier of the period-`p` map (chain rule along the orbit, `hasDerivAt_quadratic_iterate`). -/
theorem eval_deriv_fixedPointPoly (c : ℂ) (p : ℕ) (z : ℂ) :
    (derivative (fixedPointPoly c p)).eval z
      = (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1 := by
  have h1 : HasDerivAt (fun y => (fixedPointPoly c p).eval y)
      ((derivative (fixedPointPoly c p)).eval z) z := (fixedPointPoly c p).hasDerivAt z
  have hiter : HasDerivAt (fun y => (quadratic c)^[p] y)
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) z := hasDerivAt_quadratic_iterate c z p
  have h2 : HasDerivAt (fun y => (fixedPointPoly c p).eval y)
      ((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1) z := by
    have heq : (fun y => (fixedPointPoly c p).eval y) = fun y => (quadratic c)^[p] y - y := by
      funext y; rw [fixedPointPoly_eval]
    rw [heq]; exact hiter.sub (hasDerivAt_id z)
  exact h1.unique h2

/-- **The holomorphic fixed-point index formula for `f_c^[p]`.** If `f_c^[p] - X` is separable (no
parabolic, i.e. multiplier-`1`, fixed point of period dividing `p`) and `p ≥ 1`, the sum of the
fixed-point indices `1/(λ_z - 1)` over the fixed points of `f_c^[p]` vanishes, where
`λ_z = ∏_{k<p} 2·f_c^[k] z` is the cycle multiplier. Equivalently `∑ 1/(1 - λ_z) = 0`. This is the
algebraic constraint on the whole period-`p` multiplier spectrum that the resonance pinning
(`resonance_order`) must contradict on the Zdunik-free route to the connected-case obstruction. -/
theorem sum_index_fixedPoints_eq_zero (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable) :
    ∑ z ∈ (fixedPointPoly c p).roots.toFinset,
      ((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹ = 0 := by
  have hd : 2 ≤ (fixedPointPoly c p).natDegree := by
    rw [fixedPointPoly_natDegree c hp]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  have hkey := sum_inv_deriv_eq_zero hsep hd
  rw [← hkey]
  apply Finset.sum_congr rfl
  intro z _
  rw [eval_deriv_fixedPointPoly]

/-- `(2:ℂ)^p ≠ 1` for `p ≥ 1` (its modulus is `2^p ≥ 2`). -/
theorem two_pow_complex_ne_one {p : ℕ} (hp : 1 ≤ p) : (2 : ℂ) ^ p ≠ 1 := by
  intro h
  have hn : ‖(2 : ℂ) ^ p‖ = 1 := by rw [h, norm_one]
  rw [norm_pow, Complex.norm_two] at hn
  have hge : (2 : ℝ) ^ p ≥ 2 := by
    calc (2 : ℝ) ^ p ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hp
      _ = 2 := pow_one 2
  linarith

/-- **Index-formula corollary: the period-`p` multiplier spectrum is non-degenerate.** If `f_c^[p] - X` is
separable (no parabolic period-`p` cycle) and `p ≥ 1`, then **not** every fixed point of `f_c^[p]` has
multiplier exactly `2^p`: at least one fixed point `z` has `λ_z = ∏_{k<p} 2·f_c^[k] z ≠ 2^p`. Were all
`2^p` of them equal to `2^p`, the index sum would be `2^p · (2^p - 1)⁻¹ ≠ 0`, contradicting
`sum_index_fixedPoints_eq_zero`. This is precisely the obstruction to the resonance pinning
(`resonance_order`) holding in its generic `λ = 2^p` form across the whole cycle — the algebraic seed of
the Zdunik-free route. -/
theorem exists_fixedPoint_multiplier_ne_two_pow (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable) :
    ∃ z ∈ (fixedPointPoly c p).roots.toFinset,
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (2 : ℂ) ^ p := by
  by_contra hcon
  have hall : ∀ z ∈ (fixedPointPoly c p).roots.toFinset,
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p := by
    intro z hz; by_contra hne; exact hcon ⟨z, hz, hne⟩
  have hsum := sum_index_fixedPoints_eq_zero c hp hsep
  have hrw : ∑ z ∈ (fixedPointPoly c p).roots.toFinset,
      ((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹
      = ∑ _z ∈ (fixedPointPoly c p).roots.toFinset, (((2 : ℂ) ^ p) - 1)⁻¹ :=
    Finset.sum_congr rfl fun z hz => by rw [hall z hz]
  rw [hrw, Finset.sum_const] at hsum
  have hcard : (fixedPointPoly c p).roots.toFinset.card = 2 ^ p := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      fixedPointPoly_natDegree c hp]
  rw [hcard, nsmul_eq_mul] at hsum
  have h2p1 : ((2 : ℂ) ^ p) - 1 ≠ 0 := sub_ne_zero.mpr (two_pow_complex_ne_one hp)
  have h2pnat : ((2 ^ p : ℕ) : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  rw [h2pnat] at hsum
  exact (mul_ne_zero (pow_ne_zero p (two_ne_zero)) (inv_ne_zero h2p1)) hsum

/-! ### Layer 3 — the quantitative split (bulk vs. exceptional set) -/

/-- **Index-formula split.** Partition the fixed points of `f_c^[p]` into an "exceptional" finite set `B`
and the rest `roots ∖ B`, where every point of `roots ∖ B` has multiplier exactly `2^p`. The index formula
becomes the balance `card(roots∖B)·(2^p-1)⁻¹ + ∑_{z∈B} (λ_z-1)⁻¹ = 0`: the pinned bulk contributes a real
mass `card(roots∖B)/(2^p-1)` that the exceptional indices must cancel. -/
theorem index_formula_split (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hB : B ⊆ (fixedPointPoly c p).roots.toFinset)
    (hG : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p) :
    (((fixedPointPoly c p).roots.toFinset \ B).card : ℂ) * ((2 : ℂ) ^ p - 1)⁻¹
      + ∑ z ∈ B, ((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹ = 0 := by
  have hsum := sum_index_fixedPoints_eq_zero c hp hsep
  rw [← Finset.sum_sdiff hB] at hsum
  have hrw : ∑ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
      ((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹
      = ∑ _z ∈ (fixedPointPoly c p).roots.toFinset \ B, (((2 : ℂ) ^ p) - 1)⁻¹ :=
    Finset.sum_congr rfl fun z hz => by rw [hG z hz]
  rw [hrw, Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum

/-- **The pinned bulk is dominated by the exceptional mass.** Under the split of `index_formula_split`, the
number of pinned fixed points (those with multiplier `2^p`) is bounded by the total exceptional index mass
times `2^p-1`:
`card(roots∖B) ≤ (2^p-1)·∑_{z∈B} ‖(λ_z-1)⁻¹‖`. When the exceptional indices are small (the dynamically
expected case off an attracting fixed point — far-out repelling fixed points of `f` have multiplier
`(2z*)^p → ∞`, so `(λ_z-1)⁻¹ → 0`), the bulk `2^p - card(B)` cannot fit under this bound for large `p`,
contradicting the existence of the relation that pins the bulk. This is the quantitative engine of the
Zdunik-free obstruction. -/
theorem card_bulk_le (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hB : B ⊆ (fixedPointPoly c p).roots.toFinset)
    (hG : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p) :
    (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)
      ≤ ((2 : ℝ) ^ p - 1) *
        ∑ z ∈ B, ‖((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹‖ := by
  set G := ((fixedPointPoly c p).roots.toFinset \ B).card with hGdef
  set S := ∑ z ∈ B, ((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹ with hSdef
  set T := ∑ z ∈ B, ‖((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹‖ with hTdef
  have hsplit := index_formula_split c hp hsep B hB hG
  have heq : (G : ℂ) * ((2 : ℂ) ^ p - 1)⁻¹ = -S := eq_neg_of_add_eq_zero_left hsplit
  have hnorm := congrArg norm heq
  rw [norm_mul, norm_inv, Complex.norm_natCast, norm_neg] at hnorm
  have hd : ‖(2 : ℂ) ^ p - 1‖ = (2 : ℝ) ^ p - 1 := by
    have hcast : (2 : ℂ) ^ p - 1 = (((2 : ℝ) ^ p - 1 : ℝ) : ℂ) := by push_cast; ring
    have hge : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num)
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hd] at hnorm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
    have h2 : (2 : ℝ) ^ p ≥ 2 := by
      calc (2 : ℝ) ^ p ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hp
        _ = 2 := pow_one 2
    linarith
  have key : (G : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ ≤ T := by rw [hnorm]; exact norm_sum_le _ _
  calc (G : ℝ) = ((G : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹) * ((2 : ℝ) ^ p - 1) := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
    _ ≤ T * ((2 : ℝ) ^ p - 1) := mul_le_mul_of_nonneg_right key (le_of_lt hpos)
    _ = ((2 : ℝ) ^ p - 1) * T := mul_comm _ _

/-- The fixed-point polynomial of `f_c^[p]` has exactly `2^p` distinct roots (separable, degree `2^p`). -/
theorem fixedPointPoly_roots_card (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable) :
    (fixedPointPoly c p).roots.toFinset.card = 2 ^ p := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    fixedPointPoly_natDegree c hp]

/-- **The exceptional-set contradiction (Zdunik-free engine, final form).** If the period-`p` cycle splits
into a pinned bulk (multiplier `2^p`) and a finite exceptional set `B` whose total index mass is too small
to balance the bulk — `(2^p-1)·∑_{z∈B} ‖(λ_z-1)⁻¹‖ < card(roots∖B)` — then `False`. Immediate from
`card_bulk_le`. This is the algebraic endpoint of the route: the entire connected-case obstruction (for
parameters where the exceptional mass is small — i.e. no attracting fixed point pulls an index term to
`-1`) is reduced to the three dynamical facts that (i) `B` is finite, (ii) every non-`B` cycle point is
pinned to multiplier `2^p` by a continuation (`resonance_order`), and (iii) the `B`-indices are small. -/
theorem false_of_exceptional_mass_small (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hB : B ⊆ (fixedPointPoly c p).roots.toFinset)
    (hG : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p)
    (hsmall : ((2 : ℝ) ^ p - 1) *
        ∑ z ∈ B, ‖((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹‖
      < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    False :=
  absurd (card_bulk_le c hp hsep B hB hG) (not_le.mpr hsmall)

end Bottcher
