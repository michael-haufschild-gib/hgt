import GaloisForLFunctions.ArithmeticCorrelationGeometry.AlmostEveryGaugePointCancelsToTheSquareRoot
import GaloisForLFunctions.RHTower.FormationPotentialCriterion
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# The hull over the torus

Limits of vertical translates of `ζ` fibre over the prime torus: on `Re s > 1` such a limit is the Dirichlet series `L_ω(s) = Σ ω(n) n^{−s}` of a
completely multiplicative unimodular `ω`. Over which torus points does the fibre extend into the strip, and which of those carry zeros?

| Torus point | Continuation into the strip | Zeros |
|---|---|---|
| Orbit point `n^{−iu}` | `ζ(s + iu)`, a pole at `1 − iu` | the translated zeros of `ζ` |
| Finite modification of an orbit point | meromorphic, by finitely many local factors (`fibre_finite_modification`) | **exactly** the translated zeros on `Re s > 0` (`fibre_zero_iff`) |
| Liouville point `−1` | `ζ(2s)/ζ(s)`: holomorphic on `Re s > ½` **iff RH** (`riemannHypothesis_iff_liouvilleFibre_extends`) | none on `Re s > ½`, whatever happens: the zeros of `ζ` are its poles |
| Haar-almost every point | holomorphic on `Re s > ½` (`ae_fibre_extends_zeroFree`) | **none** |

So zeros sit over a Haar-null set, and the set contains the dense orbit coset as soon as `ζ` has an off-line zero. The strip exists over a typical point
by square-root cancellation of the twists; over the orbit it exists by continuation only.

And RH in the language of the hull (`riemannHypothesis_iff_limits_zeroFree`): every nonzero locally uniform limit of vertical translates on a domain in `Re s > ½` is zero-free.
-/

open Complex Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-! ### Orbit points and their finite modifications -/

/-- A prime power of a complex exponent: the Dirichlet term `n^{−s}` is completely multiplicative for `n ≠ 0`. -/
theorem natCast_cpow_neg_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n (-s)

/-- The Dirichlet coefficients `ω(n) n^{−s}` as a monoid-with-zero homomorphism. -/
def twistedHom (f : ℕ →*₀ ℂ) {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := f n * (n : ℂ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    rw [map_mul, natCast_cpow_neg_mul hm hn]
    ring

theorem twistedHom_apply (f : ℕ →*₀ ℂ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    twistedHom f hs n = f n * (n : ℂ) ^ (-s) := rfl

/-- On `Re s > 1` the twisted terms of a unimodular point are absolutely summable. -/
theorem summable_norm_twistedHom {f : ℕ →*₀ ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (hs0 : s ≠ 0) : Summable fun n => ‖twistedHom f hs0 n‖ := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) ^ s.re)⁻¹ :=
    Real.summable_nat_rpow_inv.mpr hs
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum
  rw [twistedHom_apply, norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hs0, Real.zero_rpow (by linarith : s.re ≠ 0)]
  have h1 : ‖(n : ℂ) ^ (-s)‖ = ((n : ℝ) ^ s.re)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, Real.rpow_neg (Nat.cast_nonneg n)]
  rw [h1]
  calc
    ‖f n‖ * ((n : ℝ) ^ s.re)⁻¹ ≤ 1 * ((n : ℝ) ^ s.re)⁻¹ :=
      mul_le_mul_of_nonneg_right (hf n) (by positivity)
    _ = _ := one_mul _

/-- The local factors of a unimodular point do not vanish on `Re s > 0`. -/
theorem one_sub_ne_zero_of_norm_le {p : ℕ} (hp : p.Prime) {f : ℕ →*₀ ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 0 < s.re) : 1 - f p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : f p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  have h4 := mul_le_mul_of_nonneg_right (hf p) (norm_nonneg ((p : ℂ) ^ (-s)))
  rw [one_mul] at h4
  linarith

/-- **Finite modifications.** Two unimodular points that agree off a finite set of primes have Dirichlet series differing by
local factors. -/
theorem fibre_finite_modification {f g : ℕ →*₀ ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (F : Finset Nat.Primes) (hfg : ∀ p : Nat.Primes, p ∉ F → f p = g p) {s : ℂ} (hs : 1 < s.re) :
    (∑' n, f n * (n : ℂ) ^ (-s)) * ∏ p ∈ F, (1 - f p * ((p : ℕ) : ℂ) ^ (-s)) =
      (∑' n, g n * (n : ℂ) ^ (-s)) * ∏ p ∈ F, (1 - g p * ((p : ℕ) : ℂ) ^ (-s)) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hre : 0 < s.re := by linarith
  have hpf := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (summable_norm_twistedHom hf hs hs0)
  have hpg := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (summable_norm_twistedHom hg hs hs0)
  have hne : ∀ (h : ℕ →*₀ ℂ), (∀ n, ‖h n‖ ≤ 1) → ∀ p : Nat.Primes,
      1 - twistedHom h hs0 (p : ℕ) ≠ 0 := fun h hh p =>
    one_sub_ne_zero_of_norm_le p.2 hh hre
  -- The ratio of the two Euler products is a finite product.
  set r : Nat.Primes → ℂ := fun p =>
    (1 - twistedHom f hs0 (p : ℕ)) * (1 - twistedHom g hs0 (p : ℕ))⁻¹ with hr
  have hrone : ∀ p, p ∉ F → r p = 1 := by
    intro p hp
    have e : twistedHom f hs0 (p : ℕ) = twistedHom g hs0 (p : ℕ) := by
      rw [twistedHom_apply, twistedHom_apply, hfg p hp]
    simp only [hr, e]
    exact mul_inv_cancel₀ (hne g hg p)
  have hprod : HasProd r (∏ p ∈ F, r p) := hasProd_prod_of_ne_finset_one hrone
  have hmul := hpf.mul hprod
  have hpoint : (fun p : Nat.Primes => (1 - twistedHom f hs0 (p : ℕ))⁻¹ * r p) =
      fun p : Nat.Primes => (1 - twistedHom g hs0 (p : ℕ))⁻¹ := by
    funext p
    simp only [hr]
    rw [← mul_assoc, inv_mul_cancel₀ (hne f hf p), one_mul]
  rw [hpoint] at hmul
  have huniq := hmul.unique hpg
  have hF : ∏ p ∈ F, r p =
      (∏ p ∈ F, (1 - f p * ((p : ℕ) : ℂ) ^ (-s))) * (∏ p ∈ F, (1 - g p * ((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    simp only [hr, twistedHom_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [hF] at huniq
  have hgne : ∏ p ∈ F, (1 - g p * ((p : ℕ) : ℂ) ^ (-s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => by
      have := hne g hg p
      rwa [twistedHom_apply] at this
  simp only [twistedHom_apply] at huniq
  rw [← huniq]
  field_simp

/-- The orbit point `n^{−iu}` as a completely multiplicative function. -/
def orbitPoint (u : ℝ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else (n : ℂ) ^ (-((u : ℂ) * I))
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, natCast_cpow_neg_mul hm hn]

theorem norm_orbitPoint_le (u : ℝ) (n : ℕ) : ‖orbitPoint u n‖ ≤ 1 := by
  show ‖if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-((u : ℂ) * I))‖ ≤ 1
  split_ifs with h
  · simp
  · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
    simp

/-- The fibre over an orbit point is the translate of `ζ`. -/
theorem tsum_orbitPoint {u : ℝ} {s : ℂ} (hs : 1 < s.re) :
    ∑' n, orbitPoint u n * (n : ℂ) ^ (-s) = riemannZeta (s + (u : ℂ) * I) := by
  have hre : 1 < (s + (u : ℂ) * I).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have hne : s + (u : ℂ) * I ≠ 0 := by
      intro h
      rw [h] at hre
      simp at hre
      linarith
    simp [orbitPoint, hne]
  · have h1 : orbitPoint u n = (n : ℂ) ^ (-((u : ℂ) * I)) := if_neg hn
    rw [h1, one_div, ← Complex.cpow_neg, neg_add, add_comm, Complex.cpow_add _ _ (by exact_mod_cast hn)]

/-- **The finite-type fibre on the half-plane.** A unimodular point that agrees with the orbit point `n^{−iu}` off a finite set of primes
has `L_ω(s) = ζ(s + iu) Π_{p∈F} (1 − p^{−s−iu})/(1 − ω(p) p^{−s})` on `Re s > 1`. -/
theorem tsum_finite_type {g : ℕ →*₀ ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) {u : ℝ} (F : Finset Nat.Primes)
    (hgu : ∀ p : Nat.Primes, p ∉ F → g p = orbitPoint u p) {s : ℂ} (hs : 1 < s.re) :
    ∑' n, g n * (n : ℂ) ^ (-s) = riemannZeta (s + (u : ℂ) * I) *
      ∏ p ∈ F, ((1 - orbitPoint u p * ((p : ℕ) : ℂ) ^ (-s)) * (1 - g p * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have h := fibre_finite_modification hg (norm_orbitPoint_le u) F hgu hs
  rw [tsum_orbitPoint hs] at h
  have hgne : ∏ p ∈ F, (1 - g p * ((p : ℕ) : ℂ) ^ (-s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => one_sub_ne_zero_of_norm_le p.2 hg (by linarith)
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  field_simp
  exact h

/-- **The finite-type fibre carries exactly the translated zeros of `ζ`.** On `Re s > 0` the continuation
`ζ(s + iu) Π_{p∈F}(1 − p^{−s−iu})/(1 − ω(p) p^{−s})` vanishes exactly when `ζ(s + iu)` does. -/
theorem fibre_zero_iff {g : ℕ →*₀ ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) (u : ℝ) (F : Finset Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) :
    riemannZeta (s + (u : ℂ) * I) *
      ∏ p ∈ F, ((1 - orbitPoint u p * ((p : ℕ) : ℂ) ^ (-s)) * (1 - g p * ((p : ℕ) : ℂ) ^ (-s))⁻¹) = 0 ↔
      riemannZeta (s + (u : ℂ) * I) = 0 := by
  have hprod : ∏ p ∈ F, ((1 - orbitPoint u p * ((p : ℕ) : ℂ) ^ (-s)) *
      (1 - g p * ((p : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => mul_ne_zero
      (one_sub_ne_zero_of_norm_le p.2 (norm_orbitPoint_le u) hs)
      (inv_ne_zero (one_sub_ne_zero_of_norm_le p.2 hg hs))
  simp [hprod]

/-! ### The Liouville fibre decides the Riemann hypothesis -/

/-- The half-plane `Re s > ½`. -/
abbrev rightHalf : Set ℂ := {s | 1 / 2 < s.re}

theorem isOpen_rightHalf : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalf : IsPreconnected rightHalf :=
  (convex_halfSpace_re_gt (1 / 2)).isPreconnected

/-- The fibre over the Liouville point. -/
def liouvilleFibre (s : ℂ) : ℂ := LSeries (fun n => _root_.RHTower.liouvilleC n) s

theorem differentiableAt_zeta_two_mul {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s := by
  have hne : 2 * s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact (differentiableAt_riemannZeta hne).comp s ((differentiableAt_id).const_mul 2)

/-- **The Liouville fibre decides RH.** `ζ(2s)/ζ(s)` extends holomorphically to `Re s > ½` if and only if the Riemann hypothesis holds. -/
theorem riemannHypothesis_iff_liouvilleFibre_extends :
    RiemannHypothesis ↔ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalf ∧
      ∀ s, 1 < s.re → F s = liouvilleFibre s := by
  rw [_root_.RHTower.riemannHypothesis_iff_zetaZeroFreeRight]
  constructor
  · intro hz
    have hU : ∀ s : ℂ, 1 / 2 < s.re → _root_.RHTower.zetaResidueUnit s ≠ 0 := by
      intro s hs
      by_cases h1 : s = 1
      · subst h1
        simp
      · have e : _root_.RHTower.zetaResidueUnit s = (s - 1) * riemannZeta s :=
          (_root_.RHTower.zetaResidueUnit_eventuallyEq h1).self_of_nhds
        rw [e]
        exact mul_ne_zero (sub_ne_zero.mpr h1) (hz s hs h1)
    refine ⟨fun s => riemannZeta (2 * s) * (s - 1) / _root_.RHTower.zetaResidueUnit s, ?_, ?_⟩
    · intro s hs
      have hs' : 1 / 2 < s.re := hs
      refine (DifferentiableAt.div ?_ (_root_.RHTower.analyticAt_zetaResidueUnit s).differentiableAt
        (hU s hs')).differentiableWithinAt
      exact (differentiableAt_zeta_two_mul hs').mul (differentiableAt_id.sub_const 1)
    · intro s hs
      have hs1 : s ≠ 1 := by
        rintro rfl
        simp at hs
      have hzs : riemannZeta s ≠ 0 := hz s (by linarith) hs1
      have e : _root_.RHTower.zetaResidueUnit s = (s - 1) * riemannZeta s :=
        (_root_.RHTower.zetaResidueUnit_eventuallyEq hs1).self_of_nhds
      have hL := _root_.RHTower.LSeries_liouvilleC_mul_riemannZeta hs
      simp only [liouvilleFibre]
      rw [e, ← hL]
      have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp
  · rintro ⟨F, hFd, hF⟩ ρ hρ hρ1 hzero
    set G : ℂ → ℂ := fun s => F s * _root_.RHTower.zetaResidueUnit s - (s - 1) * riemannZeta (2 * s)
      with hG
    have hGd : DifferentiableOn ℂ G rightHalf := by
      intro s hs
      have hs' : 1 / 2 < s.re := hs
      refine DifferentiableWithinAt.sub ((hFd s hs).mul
        (_root_.RHTower.analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt)
        ((differentiableAt_id.sub_const 1).mul (differentiableAt_zeta_two_mul hs')).differentiableWithinAt
    have hGa : AnalyticOnNhd ℂ G rightHalf := hGd.analyticOnNhd isOpen_rightHalf
    have hz2 : (2 : ℂ) ∈ rightHalf := by
      show 1 / 2 < (2 : ℂ).re
      norm_num
    have hev : G =ᶠ[𝓝 (2 : ℂ)] 0 := by
      have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [hopen] with s hs
      have hs1 : s ≠ 1 := by
        rintro rfl
        simp at hs
      have e : _root_.RHTower.zetaResidueUnit s = (s - 1) * riemannZeta s :=
        (_root_.RHTower.zetaResidueUnit_eventuallyEq hs1).self_of_nhds
      have hL := _root_.RHTower.LSeries_liouvilleC_mul_riemannZeta hs
      simp only [hG, Pi.zero_apply]
      rw [hF s hs, e, liouvilleFibre, ← hL]
      ring
    have hall := hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_rightHalf hz2 hev
    have hρG := hall hρ
    simp only [hG, Pi.zero_apply] at hρG
    have e : _root_.RHTower.zetaResidueUnit ρ = (ρ - 1) * riemannZeta ρ :=
      (_root_.RHTower.zetaResidueUnit_eventuallyEq hρ1).self_of_nhds
    rw [e, hzero, mul_zero, mul_zero, zero_sub, neg_eq_zero] at hρG
    have hne : riemannZeta (2 * ρ) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_le_re ?_
      simp
      linarith
    exact (mul_ne_zero (sub_ne_zero.mpr hρ1) hne) hρG

/-! ### A typical torus point is zero-free -/

/-- **Abel summation, holomorphically.** Polynomially bounded partial sums give a holomorphic sum on `Re s > α`. -/
theorem exists_analytic_abel {c : ℕ → ℂ} {C α : ℝ} (hC0 : 0 ≤ C) (hα : 0 ≤ α)
    (hC : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, c n‖ ≤ C * ((N : ℝ) + 1) ^ α) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | α < s.re} ∧
      ∀ s, α < s.re → Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
        atTop (𝓝 (F s)) := by
  classical
  set A : ℕ → ℂ := fun k => ∑ n ∈ Finset.range k, c n with hA
  set g : ℕ → ℂ → ℂ := fun i s => (((((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) - (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) *
    A (i + 1) with hg
  have htwo : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
  have hAbound : ∀ i : ℕ, ‖A (i + 1)‖ ≤ C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α := by
    intro i
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h := hC (i + 1)
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = ((i : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast] at h
    refine le_trans h ?_
    have hle : ((i : ℝ) + 1) + 1 ≤ 2 * ((i : ℝ) + 1) := by linarith
    have hmono : (((i : ℝ) + 1) + 1) ^ α ≤ (2 * ((i : ℝ) + 1)) ^ α :=
      Real.rpow_le_rpow (by positivity) hle hα
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hx.le]
    exact mul_le_mul_of_nonneg_left hmono hC0
  have hnorm : ∀ i : ℕ, ∀ s : ℂ, 0 < s.re → ‖g i s‖ ≤
      (‖s‖ * (C * (2 : ℝ) ^ α)) * ((i : ℝ) + 1) ^ (-(s.re + 1 - α)) := by
    intro i s hs
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hstep := GaloisForLFunctions.RHTower.norm_cpow_unit_diff_le hs hx
    have hrw : (((i : ℝ) + 1 + 1 : ℝ) : ℂ) = (((i : ℝ) + 2 : ℝ) : ℂ) := by
      congr 1
      ring
    rw [hrw] at hstep
    simp only [hg, norm_mul]
    calc
      _ ≤ (‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1)) * (C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α) :=
        mul_le_mul hstep (hAbound i) (norm_nonneg _) (by positivity)
      _ = (‖s‖ * (C * (2 : ℝ) ^ α)) * (((i : ℝ) + 1) ^ (-s.re - 1) * ((i : ℝ) + 1) ^ α) := by ring
      _ = _ := by
        rw [← Real.rpow_add hx]
        congr 2
        ring
  have hsummable : ∀ s : ℂ, α < s.re → Summable fun i => g i s := by
    intro s hs
    have hs0 : 0 < s.re := lt_of_le_of_lt hα hs
    refine Summable.of_norm_bounded ?_ fun i => hnorm i s hs0
    exact (GaloisForLFunctions.RHTower.summable_shift_rpow_neg (by linarith)).mul_left _
  have hopen : IsOpen {s : ℂ | α < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hlocal : SummableLocallyUniformlyOn g {s : ℂ | α < s.re} := by
    apply SummableLocallyUniformlyOn_of_locally_bounded hopen
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨fun _ => 0, summable_zero, by simp⟩
    obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
    obtain ⟨s₁, hs₁, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
    have hσ : α < s₀.re := hKsub hs₀
    refine ⟨fun i => (‖s₁‖ * (C * (2 : ℝ) ^ α)) * ((i : ℝ) + 1) ^ (-(s₀.re + 1 - α)),
      (GaloisForLFunctions.RHTower.summable_shift_rpow_neg (by linarith)).mul_left _, ?_⟩
    intro i s hs
    have hsr : s₀.re ≤ s.re := hmin hs
    have hsn : ‖s‖ ≤ ‖s₁‖ := hmax hs
    have hs0 : 0 < s.re := by
      have := hKsub hs
      exact lt_of_le_of_lt hα this
    refine (hnorm i s hs0).trans ?_
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_right hsn (by positivity)
    · exact Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) i; linarith) (by linarith)
  have hdiff : DifferentiableOn ℂ (fun s => ∑' i, g i s) {s : ℂ | α < s.re} := by
    refine hlocal.differentiableOn hopen fun i s hs => ?_
    have hx1 : (((i : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((i : ℝ) + 1) ≠ 0)
    have hx2 : (((i : ℝ) + 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((i : ℝ) + 2) ≠ 0)
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hx1)
    have h2 : DifferentiableAt ℂ (fun s : ℂ => (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hx2)
    exact (h1.sub h2).mul_const (A (i + 1))
  refine ⟨fun s => ∑' i, g i s, hdiff.analyticOnNhd hopen, fun s hs => ?_⟩
  have hs0 : 0 < s.re := lt_of_le_of_lt hα hs
  -- Abel's identity.
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hb
  have hbsucc : ∀ i : ℕ, b (i + 1) = (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
    intro i
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = (i : ℝ) + 2 := by push_cast; ring
    show (((((i + 1 : ℕ) : ℝ)) + 1 : ℝ) : ℂ) ^ (-s) = (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s)
    rw [hcast]
  have hgb : ∀ i, g i s = -((b (i + 1) - b i) * A (i + 1)) := by
    intro i
    simp only [hg, hbsucc]
    show _ = -(((((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s) - (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * A (i + 1))
    ring
  have habel : ∀ N : ℕ, (∑ n ∈ Finset.range N, c n * b n)
      = b (N - 1) * A N + ∑ i ∈ Finset.range (N - 1), g i s := by
    intro N
    have h := Finset.sum_range_by_parts b c N
    simp only [smul_eq_mul] at h
    rw [show (∑ n ∈ Finset.range N, c n * b n) = ∑ n ∈ Finset.range N, b n * c n from
      Finset.sum_congr rfl fun n _ => mul_comm _ _, h]
    simp_rw [hgb]
    rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  have hT : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), g i s) atTop (𝓝 (∑' i, g i s)) :=
    (hsummable s hs).hasSum.tendsto_sum_nat.comp (Filter.tendsto_sub_atTop_nat 1)
  have hB : Tendsto (fun N : ℕ => b (N - 1) * A N) atTop (𝓝 0) := by
    have hmajT : Tendsto (fun N : ℕ => (C * (2 : ℝ) ^ α) * ((N : ℝ)) ^ (-(s.re - α)))
        atTop (𝓝 0) := by
      have h := (GaloisForLFunctions.RHTower.tendsto_rpow_neg_nat_atTop (show (0 : ℝ) < s.re - α by linarith)).const_mul
        (C * (2 : ℝ) ^ α)
      simpa using h
    refine squeeze_zero_norm' ?_ hmajT
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (1 : ℕ) ≤ N := hN
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      have hval : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN]
        norm_num
      rw [hval]
      ring
    have hbnorm : ‖b (N - 1)‖ = (N : ℝ) ^ (-s.re) := by
      simp only [hb]
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      congr 1
    have hAn : ‖A N‖ ≤ C * (2 : ℝ) ^ α * (N : ℝ) ^ α := by
      refine le_trans (hC N) ?_
      have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hmono : ((N : ℝ) + 1) ^ α ≤ (2 * (N : ℝ)) ^ α :=
        Real.rpow_le_rpow (by positivity) hle hα
      rw [mul_assoc, ← Real.mul_rpow (by norm_num) hNpos.le]
      exact mul_le_mul_of_nonneg_left hmono hC0
    rw [norm_mul, hbnorm]
    refine (mul_le_mul_of_nonneg_left hAn (Real.rpow_nonneg hNpos.le _)).trans (le_of_eq ?_)
    rw [show (N : ℝ) ^ (-s.re) * (C * (2 : ℝ) ^ α * (N : ℝ) ^ α)
        = (C * (2 : ℝ) ^ α) * ((N : ℝ) ^ (-s.re) * (N : ℝ) ^ α) by ring, ← Real.rpow_add hNpos]
    congr 2
    ring
  have hlim := hB.add hT
  rw [zero_add] at hlim
  exact hlim.congr fun N => (habel N).symm

/-- A logarithmic square-root bound is `O(N^{½+ε})`. -/
theorem sqrt_log_sq_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 ≤
      (2 / ε + 1) ^ 2 * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
  have hy : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hy0 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hlog := Real.log_le_rpow_div hy0.le (half_pos hε)
  have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg hy
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ (ε / 2) := Real.one_le_rpow hy (by positivity)
  have hbase : 1 + Real.log ((N : ℝ) + 1) ≤ (2 / ε + 1) * ((N : ℝ) + 1) ^ (ε / 2) := by
    have e : ((N : ℝ) + 1) ^ (ε / 2) / (ε / 2) = (2 / ε) * ((N : ℝ) + 1) ^ (ε / 2) := by
      field_simp
    rw [e] at hlog
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity) hbase 2
  have hsplit : ((2 / ε + 1) * ((N : ℝ) + 1) ^ (ε / 2)) ^ 2 = (2 / ε + 1) ^ 2 * ((N : ℝ) + 1) ^ ε := by
    rw [mul_pow, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (ε / 2)), ← Real.rpow_mul hy0.le]
    congr 3
    push_cast
    ring
  rw [hsplit] at hsq
  have hsqrt : Real.sqrt ((N : ℝ) + 1) = ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  rw [hsqrt, Real.rpow_add hy0]
  calc
    ((N : ℝ) + 1) ^ (1 / 2 : ℝ) * (1 + Real.log ((N : ℝ) + 1)) ^ 2
        ≤ ((N : ℝ) + 1) ^ (1 / 2 : ℝ) * ((2 / ε + 1) ^ 2 * ((N : ℝ) + 1) ^ ε) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- **The strip over a typical point.** If the partial sums cancel to `N^{½+ε}` for every `ε`, the Dirichlet series extends holomorphically to `Re s > ½`. -/
theorem exists_analytic_of_squareRoot {c : ℕ → ℂ}
    (hC : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, c n‖ ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + ε)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
      ∀ s ∈ rightHalf, Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
        atTop (𝓝 (F s)) := by
  classical
  have hlocal : ∀ ε : ℝ, 0 < ε → ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 / 2 + ε < s.re} ∧
      ∀ s, 1 / 2 + ε < s.re →
        Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 (F s)) := by
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hC ε hε
    exact exists_analytic_abel hC0 (by linarith) hCb
  have hconv : ∀ s ∈ rightHalf, ∃ L : ℂ,
      Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 L) := by
    intro s hs
    have hs' : 1 / 2 < s.re := hs
    obtain ⟨F, -, hF⟩ := hlocal ((s.re - 1 / 2) / 2) (by linarith)
    exact ⟨F s, hF s (by linarith)⟩
  refine ⟨fun s => limUnder atTop
    (fun N => ∑ n ∈ Finset.range N, c n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)), ?_, ?_⟩
  · intro s hs
    have hs' : 1 / 2 < s.re := hs
    obtain ⟨F, hFa, hF⟩ := hlocal ((s.re - 1 / 2) / 2) (by linarith)
    have hmem : s ∈ {z : ℂ | 1 / 2 + (s.re - 1 / 2) / 2 < z.re} := by
      show 1 / 2 + (s.re - 1 / 2) / 2 < s.re
      linarith
    have hopen : IsOpen {z : ℂ | 1 / 2 + (s.re - 1 / 2) / 2 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    refine (hFa s hmem).congr ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact (hF z hz).limUnder_eq.symm
  · intro s hs
    obtain ⟨L, hL⟩ := hconv s hs
    have e := hL.limUnder_eq
    beta_reduce
    rw [e]
    exact hL

open ArithmeticCorrelationGeometry in
/-- The fibre of a torus point: the twisted Dirichlet series `Σ χ_x(n) n^{−s}`. -/
def gaugeFibre (x : GaugeTorus) (s : ℂ) : ℂ := LSeries (twist x) s

open ArithmeticCorrelationGeometry in
/-- The partial Dirichlet sums of a bounded coefficient tend to its L-series on `Re s > 1`. -/
theorem tendsto_partial_LSeries {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, f (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries f s)) := by
  have hsum : LSeriesSummable f s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => ?_⟩
    simpa using hf n
  have hshift := (hasSum_nat_add_iff' (f := LSeries.term f s) 1).mpr hsum.hasSum
  simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at hshift
  refine hshift.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => ?_
  have hn : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  congr 2
  push_cast
  rfl

open ArithmeticCorrelationGeometry in
/-- The twist of the Möbius function inverts the twist. -/
theorem LSeries_twist_mul_moebius (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twist x) s *
      LSeries (fun n => (ArithmeticFunction.moebius n : ℂ) * twist x n) s = 1 := by
  set g : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ) * twist x n with hg
  have hf : LSeriesSummable (twist x) s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => ?_⟩
    simpa using (norm_twist x n).le
  have hgg : LSeriesSummable g s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => ?_⟩
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := n)
      have h2 : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by exact_mod_cast this
      simpa using h2
    simpa [hg, norm_mul, norm_twist] using hμ
  have hδ : LSeries LSeries.delta s = 1 := by
    rw [LSeries_delta]
    rfl
  rw [← LSeries_convolution' hf hgg, ← hδ]
  refine LSeries_congr (fun {n} hn => ?_) s
  rw [LSeries.convolution_def]
  beta_reduce
  have hterm : ∀ p ∈ n.divisorsAntidiagonal, twist x p.1 * g p.2 =
      (ArithmeticFunction.moebius p.2 : ℂ) * twist x n := by
    intro p hp
    obtain ⟨h1, h2⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : p.1 ≠ 0 := left_ne_zero_of_mul (h1 ▸ hn)
    have hp2 : p.2 ≠ 0 := right_ne_zero_of_mul (h1 ▸ hn)
    simp only [hg]
    rw [← h1, twist_mul x hp1 hp2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hzeta : ∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.2 : ℂ) =
      if n = 1 then 1 else 0 := by
    have h1 := congrArg (fun F : ArithmeticFunction ℤ => ((F n : ℤ) : ℂ))
      ArithmeticFunction.coe_zeta_mul_moebius
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h1
    rw [show (∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.2 : ℂ)) =
      ((∑ p ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) p.1) *
        ArithmeticFunction.moebius p.2 : ℤ) : ℂ) from ?_]
    · rw [h1]
      split_ifs <;> simp
    · push_cast
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨h3, h4⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1 : p.1 ≠ 0 := left_ne_zero_of_mul (h3 ▸ hn)
      simp [ArithmeticFunction.zeta_apply, hp1]
  rw [hzeta, LSeries.delta]
  by_cases h1 : n = 1
  · subst h1
    simp [twist_one]
  · simp [h1]

open ArithmeticCorrelationGeometry in
/-- **Haar-typical points carry no zero.** For almost every torus point the fibre extends holomorphically to `Re s > ½` and has no zero there. -/
theorem ae_fibre_extends_zeroFree :
    ∀ᵐ x ∂gaugeHaar, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
      (∀ s, 1 < s.re → F s = gaugeFibre x s) ∧ ∀ s ∈ rightHalf, F s ≠ 0 := by
  have h1 := ae_exists_norm_gaugePartialSum_le (fun _ => (1 : ℂ)) (fun _ => by simp)
  have h2 := ae_exists_norm_gaugePartialSum_le (fun n => (ArithmeticFunction.moebius n : ℂ))
    (fun n => by
      have := ArithmeticFunction.abs_moebius_le_one (n := n)
      have h2 : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by exact_mod_cast this
      simpa using h2)
  filter_upwards [h1, h2] with x hx1 hx2
  obtain ⟨C₁, hC₁0, hC₁⟩ := hx1
  obtain ⟨C₂, hC₂0, hC₂⟩ := hx2
  -- The partial sums of the two series, rewritten over `range`.
  have hsum : ∀ (a : ℕ → ℂ) (N : ℕ), ∑ n ∈ Finset.range N, (a (n + 1) * twist x (n + 1)) =
      gaugePartialSum a N x := by
    intro a N
    unfold gaugePartialSum twistSum
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n => a n * twist x n) 0 N 1]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hbound : ∀ {a : ℕ → ℂ} {C : ℝ}, 0 ≤ C →
      (∀ N : ℕ, ‖gaugePartialSum a N x‖ ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2) →
      ∀ ε : ℝ, 0 < ε → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℕ,
        ‖∑ n ∈ Finset.range N, (a (n + 1) * twist x (n + 1))‖ ≤ C' * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    intro a C hC hb ε hε
    refine ⟨C * (2 / ε + 1) ^ 2, by positivity, fun N => ?_⟩
    rw [hsum]
    refine (hb N).trans ?_
    have := sqrt_log_sq_le hε N
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hC
  obtain ⟨F, hFa, hF⟩ := exists_analytic_of_squareRoot (hbound hC₁0 hC₁)
  obtain ⟨M, hMa, hM⟩ := exists_analytic_of_squareRoot (hbound hC₂0 hC₂)
  have hRe : ∀ s : ℂ, 1 < s.re → s ∈ rightHalf := fun s hs => by
    show 1 / 2 < s.re
    linarith
  have hFL : ∀ s, 1 < s.re → F s = gaugeFibre x s := by
    intro s hs
    have h3 := tendsto_partial_LSeries (f := twist x) (fun n => (norm_twist x n).le) hs
    have h4 := hF s (hRe s hs)
    simp only [one_mul] at h4
    exact tendsto_nhds_unique h4 h3
  have hML : ∀ s, 1 < s.re → M s = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ) * twist x n) s := by
    intro s hs
    have hb : ∀ n, ‖(ArithmeticFunction.moebius n : ℂ) * twist x n‖ ≤ 1 := by
      intro n
      rw [norm_mul, norm_twist, mul_one]
      have := ArithmeticFunction.abs_moebius_le_one (n := n)
      have h2 : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by exact_mod_cast this
      simpa using h2
    exact tendsto_nhds_unique (hM s (hRe s hs)) (tendsto_partial_LSeries hb hs)
  refine ⟨F, hFa, hFL, ?_⟩
  -- `F · M = 1` on the whole half-plane.
  have hprod : AnalyticOnNhd ℂ (fun s => F s * M s - 1) rightHalf :=
    (hFa.mul hMa).sub analyticOnNhd_const
  have hz2 : (2 : ℂ) ∈ rightHalf := by
    show 1 / 2 < (2 : ℂ).re
    norm_num
  have hev : (fun s => F s * M s - 1) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    simp only [Pi.zero_apply]
    rw [hFL s hs, hML s hs, gaugeFibre, LSeries_twist_mul_moebius x hs, sub_self]
  have hall := hprod.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_rightHalf hz2 hev
  intro s hs hzero
  have := hall hs
  simp only [Pi.zero_apply, hzero, zero_mul, zero_sub, neg_eq_zero] at this
  exact one_ne_zero this

/-! ### RH in the language of the hull -/

/-- **Hurwitz on a domain.** A locally uniform limit of zero-free holomorphic functions has no isolated zero. -/
theorem eventually_eq_zero_of_limit {U : Set ℂ} (hU : IsOpen U) {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Fn F atTop U) (hFn : ∀ n, DifferentiableOn ℂ (Fn n) U)
    (hF : DifferentiableOn ℂ F U) (hne : ∀ n, ∀ w ∈ U, Fn n w ≠ 0) {z : ℂ} (hz : z ∈ U)
    (hzero : F z = 0) : ∀ᶠ w in 𝓝 z, F w = 0 := by
  by_contra hcon
  have hA : AnalyticAt ℂ F z := hF.analyticAt (hU.mem_nhds hz)
  have hpunct := hA.eventually_eq_zero_or_eventually_ne_zero.resolve_left hcon
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z hz
  set r := min (δ / 2) (ρ / 2) with hr
  have hr0 : 0 < r := lt_min (half_pos hδ) (half_pos hρ)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
  have hcb : Metric.closedBall z r ⊆ U := (Metric.closedBall_subset_ball hrρ).trans hρU
  have hsphereU : Metric.sphere z r ⊆ U := Metric.sphere_subset_closedBall.trans hcb
  have hFsph : ∀ w ∈ Metric.sphere z r, F w ≠ 0 := by
    intro w hw
    have hwz : w ≠ z := by
      intro h
      rw [h, Metric.mem_sphere, dist_self] at hw
      linarith
    have hmem : w ∈ Metric.ball z δ ∩ {z}ᶜ := by
      refine ⟨Metric.mem_ball.mpr ?_, hwz⟩
      rw [Metric.mem_sphere.mp hw]
      exact hrδ
    exact hδsub hmem
  have hsne : (Metric.sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr0.le
  have hcontF : ContinuousOn (fun w => ‖F w‖) (Metric.sphere z r) :=
    (hF.continuousOn.mono hsphereU).norm
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere z r).exists_isMinOn hsne hcontF
  have hminpos : 0 < ‖F w₀‖ := norm_pos_iff.mpr (hFsph w₀ hw₀)
  have hunif : TendstoUniformlyOn Fn F atTop (Metric.closedBall z r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall z r)).mp
      (hconv.mono hcb)
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hunif) (‖F w₀‖ / 3) (by positivity)
  obtain ⟨n, hn⟩ := hclose.exists
  set g : ℂ → ℂ := fun w => Fn n w - F w with hg
  have hgne : g z ≠ 0 := by
    simp only [hg, hzero, sub_zero]
    exact hne n z hz
  have hdiffOn : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f U → DiffContOnCl ℂ f (Metric.ball z r) := by
    intro f hf
    refine ⟨hf.mono ((Metric.ball_subset_closedBall).trans hcb), ?_⟩
    rw [closure_ball z hr0.ne']
    exact hf.continuousOn.mono hcb
  have hdom : ∀ w ∈ Metric.sphere z r, 3 * ‖g w‖ ≤ ‖F w‖ := by
    intro w hw
    have h1 := hn w (Metric.sphere_subset_closedBall hw)
    have h2 : ‖F w₀‖ ≤ ‖F w‖ := hmin hw
    have h3 : ‖g w‖ = dist (F w) (Fn n w) := by
      simp only [hg, dist_eq_norm]
      rw [norm_sub_rev]
    rw [h3]
    linarith
  obtain ⟨w, hw, hwzero⟩ := HTGeometry.exists_zero_of_sphere_domination hr0
    (hdiffOn ((hFn n).sub hF)) (hdiffOn hF) hzero hgne hdom
  have : Fn n w = 0 := by
    simpa [sub_add_cancel] using hwzero
  exact hne n w (hcb hw) this

/-- **RH is the zero-freeness of the hull.** The Riemann hypothesis holds if and only if every locally uniform limit of vertical translates of `ζ`, on a domain in `Re s > ½`
avoiding the pole, is identically zero or zero-free. -/
theorem riemannHypothesis_iff_limits_zeroFree :
    RiemannHypothesis ↔ ∀ (U : Set ℂ) (τ : ℕ → ℝ) (F : ℂ → ℂ), IsOpen U → IsPreconnected U →
      U ⊆ rightHalf → (∀ j, ∀ s ∈ U, s + (τ j : ℂ) * I ≠ 1) →
      TendstoLocallyUniformlyOn (fun j s => riemannZeta (s + (τ j : ℂ) * I)) F atTop U →
      (∃ a ∈ U, F a ≠ 0) → ∀ s ∈ U, F s ≠ 0 := by
  rw [_root_.RHTower.riemannHypothesis_iff_zetaZeroFreeRight]
  constructor
  · intro hz U τ F hU hUc hUsub hτ hconv ⟨a, ha, hFa⟩ s hs hzero
    have hFnd : ∀ j, DifferentiableOn ℂ (fun s => riemannZeta (s + (τ j : ℂ) * I)) U := by
      intro j w hw
      have hne := hτ j w hw
      have hshift : DifferentiableAt ℂ (fun s : ℂ => s + (τ j : ℂ) * I) w :=
        differentiableAt_id.add_const _
      exact ((differentiableAt_riemannZeta hne).comp w hshift).differentiableWithinAt
    have hFd : DifferentiableOn ℂ F U :=
      hconv.differentiableOn (Eventually.of_forall hFnd) hU
    have hFnne : ∀ j, ∀ w ∈ U, riemannZeta (w + (τ j : ℂ) * I) ≠ 0 := by
      intro j w hw
      refine hz _ ?_ (hτ j w hw)
      have : 1 / 2 < w.re := hUsub hw
      simpa using this
    have hev := eventually_eq_zero_of_limit hU hconv hFnd hFd hFnne hs hzero
    have hall := (hFd.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hs hev
    exact hFa (hall ha)
  · intro hlim ρ hρ hρ1 hzero
    -- A convex domain on one side of the real axis, containing `ρ` and a point of `Re s > 1`.
    have hreal : ρ.im ≠ 0 := by
      intro him
      have hρr : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hpos : 0 < ρ.re := by linarith
      have hU := _root_.RHTower.zetaResidueUnit_ofReal_ne_zero hpos
      rw [← hρr] at hU
      have e : _root_.RHTower.zetaResidueUnit ρ = (ρ - 1) * riemannZeta ρ :=
        (_root_.RHTower.zetaResidueUnit_eventuallyEq hρ1).self_of_nhds
      rw [e, hzero, mul_zero] at hU
      exact hU rfl
    have hconst : ∀ U : Set ℂ, TendstoLocallyUniformlyOn
        (fun (_ : ℕ) s => riemannZeta (s + ((0 : ℝ) : ℂ) * I)) riemannZeta atTop U := by
      intro U
      rw [Metric.tendstoLocallyUniformlyOn_iff]
      intro ε hε x _
      refine ⟨Set.univ, Filter.univ_mem, Eventually.of_forall fun _ y _ => ?_⟩
      simp [hε]
    rcases lt_or_gt_of_ne hreal with him | him
    · -- `ρ` below the real axis.
      refine hlim {s | 1 / 2 < s.re ∧ s.im < 0} (fun _ => 0) riemannZeta
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_im continuous_const))
        ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_lt 0)).isPreconnected
        (fun s hs => hs.1) ?_ (hconst _) ⟨2 - I, ⟨by simp; norm_num, by simp⟩, ?_⟩ ρ ⟨hρ, him⟩ hzero
      · intro _ s hs h1
        have h2 := congrArg Complex.im h1
        simp at h2
        linarith [hs.2]
      · exact riemannZeta_ne_zero_of_one_le_re (by simp)
    · -- `ρ` above the real axis.
      refine hlim {s | 1 / 2 < s.re ∧ 0 < s.im} (fun _ => 0) riemannZeta
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt continuous_const Complex.continuous_im))
        ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
        (fun s hs => hs.1) ?_ (hconst _) ⟨2 + I, ⟨by simp; norm_num, by simp⟩, ?_⟩ ρ ⟨hρ, him⟩ hzero
      · intro _ s hs h1
        have h2 := congrArg Complex.im h1
        simp at h2
        linarith [hs.2]
      · exact riemannZeta_ne_zero_of_one_le_re (by simp)

end

end GaloisForLFunctions.PrimeTorusTheory
