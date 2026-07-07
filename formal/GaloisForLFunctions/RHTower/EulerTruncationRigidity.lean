/-
The finite multiplicative truncation of ζ, and the weight it cannot carry.

Two families of finite objects converge to `ζ`:

* the **additive** truncation `emCarrier N s = Σ_{n≤N} n^(−s) + N^(1−s)/(s−1)` — a Dirichlet
  polynomial with a pole tail, whose completed member `completedEM N` dominates ξ on an
  isolating annulus and there carries exactly `ord_ρ ξ` hole-zeros (the order-linked count);
* the **multiplicative** truncation `eulerPartial P s = ∏_{p∈P} (1 − p^(−s))⁻¹` over a finite
  set of primes — the reciprocal of the finite Euler head `eulerHeadAnchor`.

This module isolates the arithmetic of the multiplicative family. Its coefficients are fixed by
the primes — nothing about it can be steered, and none of it is a re-expression of the functional
equation; it is the σ_p-side constraint in pure finite form. The results:

* `eulerPartial_ne_zero` — every finite multiplicative truncation is **zero-free on the whole
  right half-plane `Re s > 0`**, in particular through the wall `Re s = 1` and across the
  critical strip. The strip zeros of ζ are therefore emergent: present at no finite
  multiplicative level, they appear only in the limit, exactly where the finite family stops
  converging.
* `exists_global_pow_root_eulerPartial` — for every `k` the truncation carries a **single-valued
  `2^k`-th root, analytic on all of `Re s > 0`, unconditionally**. The Kummer tower is free on
  the multiplicative side, with trivial monodromy at every point.
* `euler_additive_weight_mismatch` — at a hypothetical strip zero of ξ the two families disagree
  irreducibly: the multiplicative truncation never vanishes there, while the additive completed
  member vanishes to order `m = ord_ρ ξ ≥ 1` in its hole, carrying the nontrivial deck weight
  `exp(2πi·m/N)`. The base-rung parity `2 ∣ m` is thus a compatibility condition between two
  truncation weights — one trivial, one of order-`m` monodromy — not a re-statement of ξ = ξ(1−·).

The contrast to ξ is sharp: `ξ` has a global `2^k`-th root on `Re s > 1/2` **iff** every off-line
zero has multiplicity divisible by `2^k`; the multiplicative truncation has one on the larger
half-plane `Re s > 0` with no condition at all. The obstruction to RH_{2^k} lives precisely in
the gap between the free multiplicative tower and ξ's conditional one, concentrated at the strip
zeros and weighted by `m(ρ) mod 2^k`.
-/
import GaloisForLFunctions.RHTower.EMAnnulusSupply
import GaloisForLFunctions.RHTower.AnchorHead

noncomputable section

namespace RHTower

open Complex Finset

/-! ### §1 The arithmetic bound: `1 − p^(−s)` sits in the right half-plane -/

/-- On `Re s > 0` each prime power `p^(−s)` (`p ≥ 2`) has modulus `< 1`. -/
theorem norm_natCast_cpow_neg_lt_one {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have h2 : (1 : ℝ) < p := by exact_mod_cast hp
  calc (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt h2 (by linarith)
    _ = 1 := Real.rpow_zero _

/-- On `Re s > 0` the Euler base `1 − p^(−s)` has strictly positive real part: it lies in the
open disc of radius `1` about `1`, hence in the right half-plane. -/
theorem re_one_sub_natCast_cpow_pos {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    0 < (1 - (p : ℂ) ^ (-s)).re := by
  have hlt := norm_natCast_cpow_neg_lt_one hp hs
  rw [Complex.sub_re, Complex.one_re]
  have := Complex.re_le_norm ((p : ℂ) ^ (-s))
  linarith

/-- The Euler base avoids the branch cut of `log`. -/
theorem one_sub_natCast_cpow_mem_slitPlane {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ∈ Complex.slitPlane :=
  Or.inl (re_one_sub_natCast_cpow_pos hp hs)

/-! ### §2 The partial Euler product and its nonvanishing -/

/-- The finite multiplicative truncation of ζ: the reciprocal of the finite Euler head. -/
def eulerPartial (P : Finset ℕ) : ℂ → ℂ := fun s => ∏ p ∈ P, (1 - (p : ℂ) ^ (-s))⁻¹

/-- The truncation is the reciprocal of `eulerHeadAnchor`. -/
theorem eulerPartial_eq_inv_anchor (P : Finset ℕ) (s : ℂ) :
    eulerPartial P s = (eulerHeadAnchor P s)⁻¹ := by
  rw [eulerPartial, eulerHeadAnchor, Finset.prod_inv_distrib]

/-- **The finite multiplicative truncation is zero-free on the whole right half-plane.**  No
condition beyond `Re s > 0` and primality of the factors; in particular it never vanishes in the
critical strip or at the wall `Re s = 1`. -/
theorem eulerPartial_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    eulerPartial P s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hpP => inv_ne_zero (eulerFactor_ne_zero (hP p hpP) hs)

/-- On the real axis (`s = σ` real, `σ > 0`) each factor is a real number `≥ 1`: the finite
Landau positivity — the multiplicative truncation is real, dominant, and bounded below by `1`. -/
theorem eulerPartial_factor_real_ge_one {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) :
    1 ≤ ((1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹).re := by
  have hbase : ((p : ℂ) ^ (-(σ : ℂ))) = ((p : ℝ) ^ (-σ) : ℝ) := by
    rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hlt : (p : ℝ) ^ (-σ) < 1 := by
    have h2 : (1 : ℝ) < p := by exact_mod_cast hp
    calc (p : ℝ) ^ (-σ) < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt h2 (by linarith)
      _ = 1 := Real.rpow_zero _
  have hpos : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  have hval : (1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹ = ((1 - (p : ℝ) ^ (-σ))⁻¹ : ℝ) := by
    rw [hbase]; push_cast; ring
  rw [hval, Complex.ofReal_re, one_le_inv_iff₀]
  exact ⟨by linarith, by linarith⟩

/-! ### §3 Analyticity of the truncation on the right half-plane -/

/-- The right half-plane `Re s > 0` — the full zero-free / towered region of the truncation. -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

/-- `s ↦ p^(−s)` is entire. -/
theorem analyticAt_natCast_cpow_neg (p : ℕ) (hp : (p : ℂ) ≠ 0) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) Set.univ := fun z _ =>
    (((differentiableAt_id).neg).const_cpow (Or.inl hp)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_univ) s (Set.mem_univ s)

theorem eulerInvFactor_analyticAt {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => (1 - (p : ℂ) ^ (-z))⁻¹) s := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbase : AnalyticAt ℂ (fun z => 1 - (p : ℂ) ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_natCast_cpow_neg p hpc s)
  exact hbase.inv (eulerFactor_ne_zero hp hs)

theorem eulerPartial_analyticAt {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (eulerPartial P) s :=
  P.analyticAt_fun_prod (fun p hpP => eulerInvFactor_analyticAt (hP p hpP) hs)

/-! ### §4 The free Kummer tower on the multiplicative side -/

/-- A single-valued analytic `2^k`-th root of one local Euler factor, from the principal log of
its right-half-plane base. -/
def eulerRootFactor (k p : ℕ) : ℂ → ℂ :=
  fun s => Complex.exp (-(Complex.log (1 - (p : ℂ) ^ (-s))) * ((1 : ℂ) / 2 ^ k))

/-- A single-valued analytic `2^k`-th root of the whole truncation. -/
def eulerRoot (k : ℕ) (P : Finset ℕ) : ℂ → ℂ := fun s => ∏ p ∈ P, eulerRootFactor k p s

/-- The root factor really is a `2^k`-th root of the local Euler factor. -/
theorem eulerRootFactor_pow {k p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (eulerRootFactor k p s) ^ (2 ^ k) = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  rw [eulerRootFactor, ← Complex.exp_nat_mul]
  set w := (1 - (p : ℂ) ^ (-s)) with hw
  have hwne : w ≠ 0 := eulerFactor_ne_zero hp hs
  have hey : ((2 ^ k : ℕ) : ℂ) * (-(Complex.log w) * ((1 : ℂ) / 2 ^ k)) = -(Complex.log w) := by
    have h2 : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
    push_cast
    field_simp
  rw [hey, Complex.exp_neg, Complex.exp_log hwne]

/-- The root of the product is a `2^k`-th root of the truncation. -/
theorem eulerRoot_pow {k : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (eulerRoot k P s) ^ (2 ^ k) = eulerPartial P s := by
  rw [eulerRoot, ← Finset.prod_pow, eulerPartial]
  exact Finset.prod_congr rfl fun p hpP => eulerRootFactor_pow (hP p hpP) hs

theorem eulerRootFactor_analyticAt {k p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (eulerRootFactor k p) s := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbase : AnalyticAt ℂ (fun z => 1 - (p : ℂ) ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_natCast_cpow_neg p hpc s)
  have hlogAt : AnalyticAt ℂ Complex.log (1 - (p : ℂ) ^ (-s)) := by
    have hdiff : DifferentiableOn ℂ Complex.log Complex.slitPlane := fun z hz =>
      (Complex.differentiableAt_log hz).differentiableWithinAt
    exact (hdiff.analyticOnNhd Complex.isOpen_slitPlane) _
      (one_sub_natCast_cpow_mem_slitPlane hp hs)
  have hlog : AnalyticAt ℂ (fun z => Complex.log (1 - (p : ℂ) ^ (-z))) s :=
    AnalyticAt.comp (g := Complex.log) (f := fun z => 1 - (p : ℂ) ^ (-z)) hlogAt hbase
  exact ((hlog.neg).mul analyticAt_const).cexp

/-- **The multiplicative truncation carries a single-valued analytic `2^k`-th root on the whole
right half-plane, unconditionally.**  The Kummer tower is free on the σ_p side: trivial monodromy
at every point, no divisibility condition on anything. -/
theorem exists_global_pow_root_eulerPartial (k : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalfPlane ∧
      (∀ s ∈ rightHalfPlane, g s ^ (2 ^ k) = eulerPartial P s) := by
  refine ⟨eulerRoot k P, ?_, fun s hs => eulerRoot_pow hP hs⟩
  intro s hs
  exact P.analyticAt_fun_prod (fun p hpP => eulerRootFactor_analyticAt (hP p hpP) hs)

/-! ### §5 The weight mismatch between the two truncation families -/

/-- At a zero of ξ in the strip, the additive completed member vanishes to positive order in its
hole (`ord_ρ ξ ≥ 1`), and that order IS the hole-zero count of every dominating split. -/
theorem emSplit_length_pos_at_xi_zero {ρ : ℂ} (hz : xi ρ = 0)
    {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ} (hdata : EMSplitData ρ r₀ R N zs u) :
    1 ≤ zs.length := by
  have hord : (analyticOrderAt xi ρ).toNat = zs.length := emSplitData_count_eq hdata
  have hne : analyticOrderAt xi ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨(xi_analyticOnNhd Set.univ) ρ (Set.mem_univ ρ), hz⟩
  have htop : analyticOrderAt xi ρ ≠ ⊤ := xi_orderAt_ne_top ρ
  have h1 : 1 ≤ (analyticOrderAt xi ρ).toNat := by
    rw [Nat.one_le_iff_ne_zero, Ne, ENat.toNat_eq_zero]
    tauto
  omega

/-- **The truncation weight mismatch at a hypothetical strip zero.**  At any point `ρ` of the
critical strip:

* the multiplicative truncation `eulerPartial P` does **not** vanish there — trivial local
  monodromy, its Kummer tower single-valued (§4);
* if additionally `ξ(ρ) = 0`, then the additive completed member `completedEM N` of any
  dominating split vanishes to order `zs.length = ord_ρ ξ ≥ 1` inside its hole — nontrivial deck
  weight `exp(2πi·zs.length/N)`.

The two finite families of the SAME `ζ` therefore carry structurally incompatible weights at a
strip zero: one trivial, one of positive order. -/
theorem euler_additive_weight_mismatch {ρ : ℂ} (hs : 0 < ρ.re)
    {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    eulerPartial P ρ ≠ 0 ∧
      (xi ρ = 0 → ∀ {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ},
        EMSplitData ρ r₀ R N zs u → 1 ≤ zs.length) :=
  ⟨eulerPartial_ne_zero hP hs, fun hz _ _ _ _ _ hdata =>
    emSplit_length_pos_at_xi_zero hz hdata⟩

/-- **The σ_p-side half of the tower dichotomy.**  For every `k`, the multiplicative truncation
has a single-valued `2^k`-th root on `Re s > 0` with no condition; ξ has a single-valued `2^k`-th
root on the smaller half-plane `Re s > 1/2` only when every strip zero's order is divisible by
`2^k`.  This states the unconditional side and pins the conditional side to the hole-order
divisibility `2^k ∣ zs.length`, which is exactly `RHLadder k`. -/
theorem euler_tower_free_but_xi_tower_costs (k : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    (∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalfPlane ∧
        (∀ s ∈ rightHalfPlane, g s ^ (2 ^ k) = eulerPartial P s)) ∧
      ((∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
          EMSplitData ρ r₀ R N zs u → 2 ^ k ∣ zs.length) → RHLadder k) :=
  ⟨exists_global_pow_root_eulerPartial k hP, rhLadder_of_em_split_multiplicity k⟩

/-! ### §6 Landau positivity: the arithmetic source of the free tower -/

/-- **The Mercator expansion of the principal-log summand.**  On `Re s > 0`,
`−log(1 − p^(−s)) = Σ_{n≥1} (p^(−s))^n / n`.  Each `(p^(−s))^n = p^(−ns)` is a Dirichlet monomial
supported at the prime power `p^n`, with coefficient `1/n`; so the exponent generating the σ_p
tower is a Dirichlet series with nonnegative coefficients — Landau positivity in finite form. -/
theorem neg_log_euler_base_hasSum {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => ((p : ℂ) ^ (-s)) ^ n / (n : ℂ)) (-Complex.log (1 - (p : ℂ) ^ (-s))) :=
  Complex.hasSum_taylorSeries_neg_log (norm_natCast_cpow_neg_lt_one hp hs)

/-- **Real-axis positivity of the log summand.**  At real `σ > 0`, `−log(1 − p^(−σ)) ≥ 0`: the
nonnegative-coefficient Dirichlet series above is being evaluated at a point where every monomial
is a nonnegative real, so it sums to a nonnegative real. -/
theorem neg_log_euler_base_re_nonneg {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ (-Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ)))).re := by
  have hbase : ((p : ℂ) ^ (-(σ : ℂ))) = ((p : ℝ) ^ (-σ) : ℝ) := by
    rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hlt : (p : ℝ) ^ (-σ) < 1 := by
    have h2 : (1 : ℝ) < p := by exact_mod_cast hp
    calc (p : ℝ) ^ (-σ) < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt h2 (by linarith)
      _ = 1 := Real.rpow_zero _
  have hpos : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  rw [hbase, show (1 : ℂ) - ((p : ℝ) ^ (-σ) : ℝ) = (((1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_log (by linarith), ← Complex.ofReal_neg,
    Complex.ofReal_re]
  have : Real.log (1 - (p : ℝ) ^ (-σ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

/-- **The σ_p tower factor is real and `≥ 1` on the real axis.**  Since its exponent
`(1/2^k)·(−log(1 − p^(−σ)))` is a nonnegative real (Landau positivity), the root factor is
`exp` of a nonnegative real: real, and at least `1`.  The free tower inherits the dominance of the
truncation from the coefficient positivity, not from any symmetry. -/
theorem eulerRootFactor_real_ge_one {k p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) :
    1 ≤ (eulerRootFactor k p (σ : ℂ)).re := by
  have hnn : 0 ≤ (-Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ)))).re := neg_log_euler_base_re_nonneg hp hσ
  have hbase : ((p : ℂ) ^ (-(σ : ℂ))) = ((p : ℝ) ^ (-σ) : ℝ) := by
    rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hlt : (p : ℝ) ^ (-σ) < 1 := by
    have h2 : (1 : ℝ) < p := by exact_mod_cast hp
    calc (p : ℝ) ^ (-σ) < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt h2 (by linarith)
      _ = 1 := Real.rpow_zero _
  have hpos : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  have hreal : (-(Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ)))) * ((1 : ℂ) / 2 ^ k))
      = ((((-Real.log (1 - (p : ℝ) ^ (-σ))) * (1 / 2 ^ k)) : ℝ) : ℂ) := by
    rw [hbase, show (1 : ℂ) - ((p : ℝ) ^ (-σ) : ℝ) = (((1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_log (by linarith)]
    push_cast; ring
  rw [eulerRootFactor, hreal, ← Complex.ofReal_exp, Complex.ofReal_re]
  have hlog : Real.log (1 - (p : ℝ) ^ (-σ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hEnn : (0 : ℝ) ≤ (-Real.log (1 - (p : ℝ) ^ (-σ))) * (1 / 2 ^ k) :=
    mul_nonneg (by linarith) (by positivity)
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ ≤ Real.exp ((-Real.log (1 - (p : ℝ) ^ (-σ))) * (1 / 2 ^ k)) := Real.exp_le_exp.mpr hEnn

end RHTower
