import GaloisForLFunctions.CountingHolography.ModularConjugationIsNotThePartnerInvolution
import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.InterTowerCouplingRigidity
import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicGlobalCarrier
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Half-sided modular inclusions cannot carry the Hecke clock of `ζ`

In any standard-form von Neumann algebra `(H, M, Ω, J)`, requiring `J` to invert shifts internally
on `M` collapses the shifts to the center with `J Z J = Z*` (`StandardForm.tomita_central_eq_star`).
Borchers–Wiesbrock half-sided modular inclusions `U(a) M U(-a) ⊆ M` (`a ≥ 0`) avoid central collapse
by placing `U(a)` outside `M` with positive generator, `U(a) Ω = Ω`, `J U(a) J = U(-a)`, and modular
scaling `Δ(s) U(a) Δ(-s) = U(e^{-2πs} a)`. This module classifies all surviving partner realizations
and proves unconditionally that no half-sided modular inclusion carries either a nontrivial graph
black hole or Weil's `integerProbe` over `ℤ`:

* **Antiunitary generator–correlation dichotomy** (`posGen_eq_zero_of_comm_antiunitaryInvol`,
  `StandardForm.naturalCone_partner_hankel`). A self-adjoint positive generator whose unitary group
  commutes with an antiunitary involution `J` vanishes identically (`J P J = -P`). Inverting shifts
  under `J` (`J U(s) J = U(s)*`) preserves generator positivity (`J P J = P`) at the cost of turning
  cross-horizon natural-cone correlations on `α_s(A₀) = U(s) A₀ U(s)*` with `U(s) Ω = Ω` into
  multiplicative Hankel kernels `⟪(A₀*) Ω, U(s t)* J B₀ Ω⟫`.
* **Square-class classification, `M₂(ℂ)` realization, and continuous/Laplace collapse**
  (`isMulHankel_and_heckeInv_iff_sqClass`, `mulHankel_heckeInv_iff_factorsThrough_sqFreeCore`,
  `exists_nontrivial_vacuumFixing_partner_standardForm_heckeInv`,
  `const_of_mulHankel_eq_logToeplitz`, `const_of_sqClass_laplaceMeasure`). Kernels on `ℕ+ × ℕ+` that
  are simultaneously multiplicatively Hankel and Hecke-dilation invariant are classified by functions
  of the squarefree core `sqFreeCore (m * n)` (`ℚ_{>0} / (ℚ_{>0})²`). Nonconstant positive examples
  exist on `M₂(ℂ)` via 2-adic parity conjugation escaping `M ∪ M'`, whereas every continuous
  log-Toeplitz profile `Φ(log(m/n)) = g(m n)` and every positive-energy Laplace profile supported on
  `[0, ∞)` collapses to a constant.
* **Borchers `ax + b` spectral and Bohr-frequency rigidity**
  (`BorchersPair.eigenmode_eq_zero`, `BorchersPair.eigenvector_eq_zero_of_ne_one`,
  `BorchersPair.trivial_on_finiteDimensional`, `BorchersPair.no_nontrivial_borchers_on_quadraticAlgebra`,
  `BorchersPair.alternating_cesaro_tendsto_zero`). In any strongly continuous unitary `BorchersPair`,
  `Δ(s) U(a) Δ(-s) = U(e^{-2πs} a)` excludes every non-identity eigenvalue of `U(a)` (`a ≠ 0`),
  forcing `U` to act trivially on every finite-dimensional invariant subspace (in particular on every
  graph black hole `QuadraticAlgebra ℝ (-q) t`) and annihilating all alternating Cesàro Bohr averages
  `(1/K) ∑_{k < K} (-1)^k ⟪ψ, U(k π / γ) ψ⟫ → 0` (`γ ≠ 0`).
* **Unconditional impossibility over `ℤ` and partner standard-form trichotomy**
  (`no_vacuumFixing_partner_tateLimit_integerProbe`, `no_borchers_gns_tateLimit_integerProbe`,
  `no_halfSided_modular_inclusion_carries_integerProbe`, `partner_standardForm_trichotomy`). Neither
  the cross-horizon natural-cone form of a vacuum-fixing partner semigroup nor the one-sided GNS
  Hilbert norm of a Borchers pair can have Tate limit `integerProbe`: the former collapses
  `splineCorr` to a constant against `exists_coprimeCrossDiff_ratCorr_ne_zero`, while the latter
  forces `RiemannHypothesis`, turning `splineCorr` into an atomic critical-line Bohr series with a
  strictly positive alternating Cesàro average at any seen critical zero (`criticalSeen_infinite`).
-/

set_option autoImplicit false

open Complex Filter Topology Finset Matrix MeasureTheory
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography ArithmeticPositiveDuality
open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.RenormalizedIntersectionTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx rightZeros)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

/-! ### 1. Antiunitary generator–correlation dichotomy and cross-horizon Hankel law -/

/-- Any antiunitary involution on a complex Hilbert space is a continuous `ℝ`-linear isometry. -/
def AntiunitaryInvol.toRealCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (J : AntiunitaryInvol H) : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := J
      map_add' := J.map_add
      map_smul' := fun (r : ℝ) (x : H) => by
        have hr : ∀ y : H, r • y = (r : ℂ) • y := fun y => by
          rw [← one_smul ℂ y, ← smul_assoc, Complex.real_smul, mul_one]
        rw [hr x, J.map_smul, Complex.conj_ofReal, ← hr (J x)] }
    1
    (fun x => by simp [J.norm_map])

@[simp] theorem AntiunitaryInvol.toRealCLM_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (J : AntiunitaryInvol H) (x : H) :
    J.toRealCLM x = J x := rfl

/-- **Commuting positive-energy collapse.** If a family of operators `U(a)` commutes with an
antiunitary involution `J` (`J (U(a) (J x)) = U(a) x`) and has strong derivative `i P x` at `a = 0`
for a positive self-adjoint operator `P`, then `P = 0`: antiunitarity flips `i` to `-i`, forcing
`J P J = -P` and collapsing the nonnegative quadratic form `Re ⟪x, P x⟫` to zero. -/
theorem posGen_eq_zero_of_comm_antiunitaryInvol {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (J : AntiunitaryInvol H)
    (U : ℝ → H →L[ℂ] H) (P : H →L[ℂ] H)
    (hcomm : ∀ (a : ℝ) (x : H), J (U a (J x)) = U a x)
    (hsa : star P = P)
    (hpos : ∀ x : H, 0 ≤ (inner ℂ x (P x)).re)
    (hderiv : ∀ x : H, HasDerivAt (fun a : ℝ => U a x) (Complex.I • P x) 0) :
    P = 0 := by
  have hanti : ∀ x : H, P (J x) = -J (P x) := fun x => by
    have hd1 : HasDerivAt (fun a : ℝ => J.toRealCLM (U a x))
        (J.toRealCLM (Complex.I • P x)) 0 :=
      J.toRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hderiv x)
    have hfun : (fun a : ℝ => J.toRealCLM (U a x)) = fun a : ℝ => U a (J x) := by
      ext a
      simpa [J.invol] using hcomm a (J x)
    rw [hfun] at hd1
    have heq : J (Complex.I • P x) = Complex.I • P (J x) := hd1.unique (hderiv (J x))
    rw [J.map_smul, conj_I, _root_.neg_smul] at heq
    have hmul := congr_arg (fun v : H => Complex.I • v) heq
    simp only [smul_neg, smul_smul, Complex.I_mul_I, _root_.neg_smul, one_smul, neg_neg] at hmul
    exact neg_eq_iff_eq_neg.mp hmul.symm
  have hsym : ∀ x y : H, inner ℂ (P x) y = inner ℂ x (P y) := fun x y => by
    calc inner ℂ (P x) y = inner ℂ x (ContinuousLinearMap.adjoint P y) :=
          ContinuousLinearMap.adjoint_inner_right P x y
      _ = inner ℂ x ((star P) y) := by rw [← ContinuousLinearMap.star_eq_adjoint]
      _ = inner ℂ x (P y) := by rw [hsa]
  have hquad : ∀ x : H, inner ℂ x (P x) = 0 := fun x => by
    have h1 := hpos x
    have h2 := hpos (J x)
    have hJ : inner ℂ (J x) (P (J x)) = -inner ℂ (P x) x := by
      rw [hanti x, inner_neg_right, J.inner_map]
    rw [hsym x x] at hJ
    have hre : (inner ℂ (J x) (P (J x))).re = -(inner ℂ x (P x)).re := by
      rw [hJ, Complex.neg_re]
    have hre0 : (inner ℂ x (P x)).re = 0 := by linarith
    have him0 : (inner ℂ x (P x)).im = 0 := by
      have hconj : starRingEnd ℂ (inner ℂ x (P x)) = inner ℂ x (P x) := by
        rw [inner_conj_symm, hsym x x]
      exact Complex.conj_eq_iff_im.mp hconj
    exact Complex.ext hre0 him0
  ext y
  have hpol : ∀ x : H, inner ℂ x (P y) = 0 := fun x => by
    have hp1 := hquad (x + y)
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hquad x, hquad y,
      zero_add, add_zero] at hp1
    have hp2 := hquad (x + Complex.I • y)
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      conj_I, hquad x, hquad y] at hp2
    simp only [mul_zero, zero_add, add_zero] at hp2
    have hcomb : (2 * Complex.I) * inner ℂ x (P y) = 0 := by
      linear_combination Complex.I * hp1 + hp2
    exact (mul_eq_zero.mp hcomb).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  simpa using inner_self_eq_zero.mp (hpol (P y))

/-- Adjoint shift `α_s(A₀) = U(s) A₀ U(s)*` of a seed observable along an operator family `U`. -/
def covShift {S H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : S → H →L[ℂ] H) (s : S) (A₀ : H →L[ℂ] H) : H →L[ℂ] H :=
  U s * A₀ * star (U s)

/-- **Cross-horizon Hankel law.** In any standard-form von Neumann algebra `(H, M, ms)`, if an
isometric representation `U` of a commutative semigroup `S` fixes `ms.Ω` and is inverted by `ms.J`
(`ms.J.conjOp (U s) = star (U s)`), then the cross-horizon natural-cone correlation of covariant
shifts `covShift U s A₀` and `covShift U t B₀` depends on `(s, t)` solely through the product
`s * t`. -/
theorem StandardForm.naturalCone_partner_hankel
    {S H : Type*} [CommSemigroup S] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (ms : StandardForm M) {U : S → H →L[ℂ] H}
    (hmul : ∀ s t : S, U (s * t) = U s * U t)
    (hiso : ∀ s : S, star (U s) * U s = 1)
    (hΩ : ∀ s : S, U s ms.Ω = ms.Ω)
    (hJ : ∀ s : S, ms.J.conjOp (U s) = star (U s))
    (A₀ B₀ : H →L[ℂ] H) (s t : S) :
    inner ℂ ms.Ω (covShift U s A₀ (ms.J.conjOp (covShift U t B₀) ms.Ω)) =
      inner ℂ ((star A₀) ms.Ω) ((star (U (s * t))) (ms.J (B₀ ms.Ω))) := by
  have hstarΩ : ∀ r : S, (star (U r)) ms.Ω = ms.Ω := fun r => by
    calc (star (U r)) ms.Ω = (star (U r)) (U r ms.Ω) := by rw [hΩ r]
      _ = (star (U r) * U r) ms.Ω := rfl
      _ = ms.Ω := by rw [hiso r]; rfl
  have hright : ms.J.conjOp (covShift U t B₀) ms.Ω = (star (U t)) (ms.J (B₀ ms.Ω)) := by
    change ms.J (U t (B₀ ((star (U t)) (ms.J ms.Ω)))) = _
    rw [ms.J_omega, hstarΩ t, ← ms.J.invol (B₀ ms.Ω)]
    change ms.J.conjOp (U t) (ms.J (B₀ ms.Ω)) = _
    rw [hJ t]
  rw [hright]
  change inner ℂ ms.Ω (U s (A₀ ((star (U s)) ((star (U t)) (ms.J (B₀ ms.Ω)))))) = _
  have hadj1 : ∀ v : H, inner ℂ ms.Ω (U s v) = inner ℂ ms.Ω v := fun v => by
    calc inner ℂ ms.Ω (U s v) = inner ℂ (ContinuousLinearMap.adjoint (U s) ms.Ω) v :=
          (ContinuousLinearMap.adjoint_inner_left (U s) ms.Ω v).symm
      _ = inner ℂ ((star (U s)) ms.Ω) v := by rw [← ContinuousLinearMap.star_eq_adjoint]
      _ = inner ℂ ms.Ω v := by rw [hstarΩ s]
  have hadj2 : ∀ v : H, inner ℂ ms.Ω (A₀ v) = inner ℂ ((star A₀) ms.Ω) v := fun v => by
    calc inner ℂ ms.Ω (A₀ v) = inner ℂ (ContinuousLinearMap.adjoint A₀ ms.Ω) v :=
          (ContinuousLinearMap.adjoint_inner_left A₀ ms.Ω v).symm
      _ = inner ℂ ((star A₀) ms.Ω) v := by rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [hadj1, hadj2]
  have hprod : (star (U s)) ((star (U t)) (ms.J (B₀ ms.Ω))) =
      (star (U (s * t))) (ms.J (B₀ ms.Ω)) := by
    change (star (U s) * star (U t)) (ms.J (B₀ ms.Ω)) = _
    rw [← star_mul, ← hmul t s, mul_comm t s]
  rw [hprod]

/-! ### 2. Square-class classification, `M₂(ℂ)` realization, and continuous/Laplace collapse -/

/-- A kernel on `ℕ+ × ℕ+` is multiplicatively Hankel if `K m n` depends only on `m * n`. -/
def IsMulHankel {α : Type*} (K : ℕ+ → ℕ+ → α) : Prop :=
  ∃ g : ℕ+ → α, ∀ m n : ℕ+, K m n = g (m * n)

/-- A kernel on `ℕ+ × ℕ+` is Hecke-dilation invariant if `K (p * m) (p * n) = K m n` for all
`p, m, n ∈ ℕ+`. -/
def IsHeckeDilationInv {α : Type*} (K : ℕ+ → ℕ+ → α) : Prop :=
  ∀ p m n : ℕ+, K (p * m) (p * n) = K m n

/-- **Square-class equivalence.** A kernel on `ℕ+ × ℕ+` is both multiplicatively Hankel and
Hecke-dilation invariant if and only if it is induced by a square-class function `g : ℕ+ → α`
satisfying `g (p² k) = g k`. -/
theorem isMulHankel_and_heckeInv_iff_sqClass {α : Type*} (K : ℕ+ → ℕ+ → α) :
    (IsMulHankel K ∧ IsHeckeDilationInv K) ↔
      ∃ g : ℕ+ → α, (∀ p k : ℕ+, g (p ^ 2 * k) = g k) ∧ ∀ m n : ℕ+, K m n = g (m * n) := by
  constructor
  · rintro ⟨⟨g, hg⟩, hinv⟩
    refine ⟨g, fun p k => ?_, hg⟩
    have hp : p ^ 2 * k = (p * 1) * (p * k) := by
      rw [mul_one, sq, mul_assoc]
    rw [hp, ← hg (p * 1) (p * k), hinv p 1 k, hg 1 k, one_mul]
  · rintro ⟨g, hsq, hg⟩
    refine ⟨⟨g, hg⟩, fun p m n => ?_⟩
    have hp : (p * m) * (p * n) = p ^ 2 * (m * n) := by
      calc (p * m) * (p * n) = (p * p) * (m * n) := mul_mul_mul_comm p m p n
        _ = p ^ 2 * (m * n) := by rw [sq]
    rw [hg, hp, hsq, ← hg]

/-- The squarefree core `d` in the unique decomposition `n = m² d` of `n : ℕ+`. -/
def sqFreeCore (n : ℕ+) : ℕ+ :=
  (RHTower.dyadicSquarefreeSquareEquiv n).1.1

/-- The square-root factor `m` in the unique decomposition `n = m² d` of `n : ℕ+`. -/
def sqRootPart (n : ℕ+) : ℕ+ :=
  (RHTower.dyadicSquarefreeSquareEquiv n).2

theorem squarefree_sqFreeCore (n : ℕ+) : Squarefree (sqFreeCore n : ℕ) :=
  (RHTower.dyadicSquarefreeSquareEquiv n).1.2

theorem sqRootPart_sq_mul_sqFreeCore (n : ℕ+) : sqRootPart n ^ 2 * sqFreeCore n = n := by
  apply Subtype.ext
  exact RHTower.dyadicSquarefreeSquareEquiv_mul n

theorem sqFreeCore_sq_mul (p k : ℕ+) : sqFreeCore (p ^ 2 * k) = sqFreeCore k := by
  apply Subtype.ext
  have h1 : (sqRootPart (p ^ 2 * k) : ℕ) ^ 2 * (sqFreeCore (p ^ 2 * k) : ℕ) =
      ((p * sqRootPart k : ℕ+) : ℕ) ^ 2 * (sqFreeCore k : ℕ) := by
    have ha := RHTower.dyadicSquarefreeSquareEquiv_mul (p ^ 2 * k)
    have hb := RHTower.dyadicSquarefreeSquareEquiv_mul k
    change (sqRootPart (p ^ 2 * k) : ℕ) ^ 2 * (sqFreeCore (p ^ 2 * k) : ℕ) =
      (p : ℕ) ^ 2 * (k : ℕ) at ha
    change (sqRootPart k : ℕ) ^ 2 * (sqFreeCore k : ℕ) = (k : ℕ) at hb
    rw [ha, ← hb]
    change (p : ℕ) ^ 2 * ((sqRootPart k : ℕ) ^ 2 * (sqFreeCore k : ℕ)) =
      ((p : ℕ) * (sqRootPart k : ℕ)) ^ 2 * (sqFreeCore k : ℕ)
    ring
  exact (RHTower.squarefree_square_decomposition_unique
    (sqFreeCore (p ^ 2 * k)).pos.ne' (sqRootPart (p ^ 2 * k)).pos.ne'
    (sqFreeCore k).pos.ne' (p * sqRootPart k).pos.ne'
    (squarefree_sqFreeCore _) (squarefree_sqFreeCore _) h1).1

/-- **Canonical factorization through the squarefree core.** Partner-Hankel Hecke-invariant kernels
on `ℕ+ × ℕ+` are in bijection with arbitrary functions on positive squarefree integers via
`(m, n) ↦ sqFreeCore (m * n)`. -/
theorem mulHankel_heckeInv_iff_factorsThrough_sqFreeCore {α : Type*} (K : ℕ+ → ℕ+ → α) :
    (IsMulHankel K ∧ IsHeckeDilationInv K) ↔
      ∃ h : RHTower.SquarefreePNat → α,
        ∀ m n : ℕ+, K m n = h (RHTower.dyadicSquarefreeSquareEquiv (m * n)).1 := by
  rw [isMulHankel_and_heckeInv_iff_sqClass]
  constructor
  · rintro ⟨g, hsq, hg⟩
    refine ⟨fun d => g d.1, fun m n => ?_⟩
    rw [hg m n]
    change g (m * n) = g (sqFreeCore (m * n))
    conv_lhs => rw [← sqRootPart_sq_mul_sqFreeCore (m * n)]
    exact hsq (sqRootPart (m * n)) (sqFreeCore (m * n))
  · rintro ⟨h, hh⟩
    refine ⟨fun n => h (RHTower.dyadicSquarefreeSquareEquiv n).1, fun p k => ?_, hh⟩
    congr 1
    apply Subtype.ext
    exact sqFreeCore_sq_mul p k

/-- Logarithmic ratios `c * log(a / b)` (`a, b ∈ ℕ+`) are dense in `ℝ` for every `c ≠ 0`. -/
theorem dense_mul_log_pnat_div {c : ℝ} (hc : c ≠ 0) :
    Dense {y : ℝ | ∃ a b : ℕ+, y = c * Real.log ((a : ℝ) / (b : ℝ))} := by
  rw [Metric.dense_iff]
  intro y ε hε
  set x₀ : ℝ := Real.exp (y / c)
  have hx₀ : 0 < x₀ := Real.exp_pos (y / c)
  have hcont : ContinuousAt (fun t : ℝ => c * Real.log t) x₀ :=
    continuousAt_const.mul (Real.continuousAt_log hx₀.ne')
  have hval : c * Real.log x₀ = y := by
    rw [Real.log_exp, mul_div_cancel₀ y hc]
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  set δ' : ℝ := min δ (x₀ / 2)
  have hδ' : 0 < δ' := lt_min hδ (half_pos hx₀)
  obtain ⟨z, ⟨q, rfl⟩, hqz⟩ :=
    Metric.mem_closure_iff.mp (Rat.denseRange_cast x₀) δ' hδ'
  have hq_pos_real : 0 < (q : ℝ) := by
    have hd : |(q : ℝ) - x₀| < x₀ / 2 := by
      rw [← Real.dist_eq, dist_comm]
      exact hqz.trans_le (min_le_right _ _)
    linarith [(abs_lt.mp hd).1]
  have hq_pos : 0 < q := by exact_mod_cast hq_pos_real
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
  let a : ℕ+ := ⟨q.num.natAbs, Int.natAbs_pos.mpr hnum_pos.ne'⟩
  let b : ℕ+ := ⟨q.den, q.den_pos⟩
  have hdiv : ((a : ℝ) / (b : ℝ)) = (q : ℝ) := by
    have ha : (a : ℝ) = (q.num : ℝ) := by
      have h1 : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum_pos.le
      exact_mod_cast h1
    have hb : (b : ℝ) = (q.den : ℝ) := rfl
    rw [ha, hb]
    exact_mod_cast Rat.num_div_den q
  refine ⟨c * Real.log ((a : ℝ) / (b : ℝ)), ?_, ⟨a, b, rfl⟩⟩
  rw [hdiv, dist_comm, ← hval]
  exact hclose (by rw [dist_comm]; exact hqz.trans_le (min_le_left _ _))

/-- **Constant collapse of continuous log-Toeplitz Hankel kernels.** Any continuous profile
`Φ : ℝ → β` into a Hausdorff space whose ratio kernel `Φ(log(m / n))` on `ℕ+ × ℕ+` depends only on
`m * n` is identically constant: `(a²)(b²) = (a b)²` forces `Φ(2 log(a / b)) = Φ(0)` on a dense
subset of `ℝ`. -/
theorem const_of_mulHankel_eq_logToeplitz {β : Type*} [TopologicalSpace β] [T2Space β]
    {Φ : ℝ → β} (hΦ : Continuous Φ) {g : ℕ+ → β}
    (heq : ∀ m n : ℕ+, Φ (Real.log ((m : ℝ) / (n : ℝ))) = g (m * n)) (y : ℝ) :
    Φ y = Φ 0 := by
  have hcl : IsClosed {z : ℝ | Φ z = Φ 0} := isClosed_eq hΦ continuous_const
  refine (hcl.closure_subset_iff.mpr ?_) (dense_mul_log_pnat_div two_ne_zero y)
  rintro _ ⟨a, b, rfl⟩
  have hlog_sq : 2 * Real.log ((a : ℝ) / (b : ℝ)) =
      Real.log (((a ^ 2 : ℕ+) : ℝ) / ((b ^ 2 : ℕ+) : ℝ)) := by
    have hcast : (((a ^ 2 : ℕ+) : ℝ) / ((b ^ 2 : ℕ+) : ℝ)) = ((a : ℝ) / (b : ℝ)) ^ 2 := by
      push_cast
      ring
    rw [hcast, Real.log_pow]
    ring
  have hprod : (a ^ 2 : ℕ+) * b ^ 2 = (a * b) * (a * b) := by
    apply Subtype.ext
    push_cast
    ring
  have hlog_diag : (0 : ℝ) = Real.log (((a * b : ℕ+) : ℝ) / ((a * b : ℕ+) : ℝ)) := by
    have hpos : (0 : ℝ) < ((a * b : ℕ+) : ℝ) := by exact_mod_cast (a * b).pos
    rw [div_self hpos.ne', Real.log_one]
  change Φ (2 * Real.log ((a : ℝ) / (b : ℝ))) = Φ 0
  rw [hlog_sq, heq (a ^ 2) (b ^ 2), hprod, ← heq (a * b) (a * b), ← hlog_diag]

/-- Euclidean / positive-energy Laplace profile `n ↦ ∫ e^{-λ log n} dμ(λ)` on `ℕ+`. -/
def laplaceProfile (μ : Measure ℝ) (n : ℕ+) : ℝ :=
  ∫ lam : ℝ, Real.exp (-lam * Real.log (n : ℝ)) ∂μ

/-- **Constant collapse of positive-energy Laplace square-class profiles.** If a finite positive
measure `μ` on `ℝ` is supported on `[0, ∞)` and its Laplace profile satisfies `g(4) = g(1)` (as
forced by any square-class invariance `g(2² · 1) = g(1)`), then `μ((0, ∞)) = 0` and `g` is
identically constant. -/
theorem const_of_sqClass_laplaceMeasure (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iio 0) = 0) (h4 : laplaceProfile μ 4 = laplaceProfile μ 1) :
    μ (Set.Ioi 0) = 0 ∧ ∀ n : ℕ+, laplaceProfile μ n = laplaceProfile μ 1 := by
  have hae_nonneg : ∀ᵐ lam : ℝ ∂μ, 0 ≤ lam := by
    rw [ae_iff]
    simpa [not_le] using hsupp
  have hint_exp : ∀ n : ℕ+, Integrable (fun lam : ℝ => Real.exp (-lam * Real.log (n : ℝ))) μ := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    refine (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [hae_nonneg] with lam hlam
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hl1 : laplaceProfile μ 1 = ∫ _ : ℝ, (1 : ℝ) ∂μ := by
    simp [laplaceProfile]
  set f : ℝ → ℝ := fun lam => 1 - Real.exp (-lam * Real.log 4)
  have hf_int : Integrable f μ := (integrable_const (1 : ℝ)).sub (by simpa using hint_exp 4)
  have hf_ae : 0 ≤ᵐ[μ] f := by
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    filter_upwards [hae_nonneg] with lam hlam
    have hexp : Real.exp (-lam * Real.log 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    show 0 ≤ 1 - Real.exp (-lam * Real.log 4)
    linarith
  have hf_zero : ∫ lam : ℝ, f lam ∂μ = 0 := by
    rw [integral_sub (integrable_const (1 : ℝ)) (by simpa using hint_exp 4)]
    have h4' : ∫ lam : ℝ, Real.exp (-lam * Real.log 4) ∂μ = ∫ _ : ℝ, (1 : ℝ) ∂μ := by
      simpa [laplaceProfile, hl1] using h4
    linarith
  have hf_ae0 : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hf_ae hf_int).mp hf_zero
  have hIoi : μ (Set.Ioi 0) = 0 := by
    refine measure_mono_null (fun lam (hlam : 0 < lam) => ?_) (ae_iff.mp hf_ae0)
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have hexp : Real.exp (-lam * Real.log 4) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    show ¬(1 - Real.exp (-lam * Real.log 4) = 0)
    linarith
  refine ⟨hIoi, fun n => ?_⟩
  rw [laplaceProfile, hl1]
  have hae0 : ∀ᵐ lam : ℝ ∂μ, lam = 0 := by
    rw [ae_iff]
    have hsub : {lam : ℝ | ¬lam = 0} ⊆ Set.Iio 0 ∪ Set.Ioi 0 := fun lam hne =>
      (lt_or_gt_of_ne hne).imp id id
    exact measure_mono_null hsub (measure_union_null hsupp hIoi)
  refine integral_congr_ae ?_
  filter_upwards [hae0] with lam hlam
  simp [hlam]

section Mat2Realization

/-- Hilbert–Schmidt `2 × 2` matrix space `ℓ²(Fin 2 × Fin 2, ℂ)`. -/
private abbrev H2 : Type := lp (fun _ : Fin 2 × Fin 2 => ℂ) 2

private theorem h2_norm_sq (X : H2) : ‖X‖ ^ 2 = ∑ p : Fin 2 × Fin 2, ‖X p‖ ^ 2 := by
  have h1 : (inner ℂ X X).re = ‖X‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), Complex.ofReal_pow, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  rw [← h1, lp.inner_eq_tsum, tsum_fintype, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), Complex.ofReal_pow, ← Complex.ofReal_pow,
    Complex.ofReal_re]

private theorem h2_entry_le_norm (X : H2) (q : Fin 2 × Fin 2) : ‖X q‖ ≤ ‖X‖ := by
  have hle : ‖X q‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [h2_norm_sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ q)
  nlinarith [norm_nonneg (X q), norm_nonneg X]

private theorem h2_norm_le_of_entry_bound (Y : H2) {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ p : Fin 2 × Fin 2, ‖Y p‖ ≤ B) : ‖Y‖ ≤ 2 * B := by
  have hsq : ‖Y‖ ^ 2 ≤ (2 * B) ^ 2 := by
    rw [h2_norm_sq]
    have hp : ∀ p : Fin 2 × Fin 2, ‖Y p‖ ^ 2 ≤ B ^ 2 := fun p => by
      nlinarith [hY p, norm_nonneg (Y p)]
    calc ∑ p : Fin 2 × Fin 2, ‖Y p‖ ^ 2
        ≤ ∑ _ : Fin 2 × Fin 2, B ^ 2 := Finset.sum_le_sum fun p _ => hp p
      _ = 4 * B ^ 2 := by simp
      _ = (2 * B) ^ 2 := by ring
  nlinarith [norm_nonneg Y]

private def leftMul2 (A : Matrix (Fin 2) (Fin 2) ℂ) : H2 →L[ℂ] H2 :=
  LinearMap.mkContinuous
    { toFun := fun X => ⟨fun p => ∑ k : Fin 2, A p.1 k * X (k, p.2),
        (Finite.of_fintype (Fin 2 × Fin 2)).memℓp _⟩
      map_add' := fun X Y => by ext p; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c X => by
        ext p
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
    (4 * ∑ q : Fin 2 × Fin 2, ‖A q.1 q.2‖)
    (fun X => by
      set S : ℝ := ∑ q : Fin 2 × Fin 2, ‖A q.1 q.2‖
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hA_le : ∀ i k : Fin 2, ‖A i k‖ ≤ S := fun i k =>
        Finset.single_le_sum (f := fun q : Fin 2 × Fin 2 => ‖A q.1 q.2‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, k))
      let Y : H2 := ⟨fun p => ∑ k : Fin 2, A p.1 k * X (k, p.2),
        (Finite.of_fintype (Fin 2 × Fin 2)).memℓp _⟩
      show ‖Y‖ ≤ (4 * S) * ‖X‖
      rw [show (4 * S) * ‖X‖ = 2 * (2 * S * ‖X‖) by ring]
      refine h2_norm_le_of_entry_bound Y (by positivity) fun p => ?_
      change ‖∑ k : Fin 2, A p.1 k * X (k, p.2)‖ ≤ 2 * S * ‖X‖
      rw [Fin.sum_univ_two, show 2 * S * ‖X‖ = S * ‖X‖ + S * ‖X‖ by ring]
      calc ‖A p.1 0 * X (0, p.2) + A p.1 1 * X (1, p.2)‖
          ≤ ‖A p.1 0‖ * ‖X (0, p.2)‖ + ‖A p.1 1‖ * ‖X (1, p.2)‖ := by
            simpa [norm_mul] using norm_add_le (A p.1 0 * X (0, p.2)) (A p.1 1 * X (1, p.2))
        _ ≤ S * ‖X‖ + S * ‖X‖ :=
            add_le_add (mul_le_mul (hA_le p.1 0) (h2_entry_le_norm X _) (norm_nonneg _) hS0)
              (mul_le_mul (hA_le p.1 1) (h2_entry_le_norm X _) (norm_nonneg _) hS0))

private def rightMul2 (B : Matrix (Fin 2) (Fin 2) ℂ) : H2 →L[ℂ] H2 :=
  LinearMap.mkContinuous
    { toFun := fun X => ⟨fun p => ∑ k : Fin 2, X (p.1, k) * B k p.2,
        (Finite.of_fintype (Fin 2 × Fin 2)).memℓp _⟩
      map_add' := fun X Y => by ext p; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by
        ext p
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
    (4 * ∑ q : Fin 2 × Fin 2, ‖B q.1 q.2‖)
    (fun X => by
      set S : ℝ := ∑ q : Fin 2 × Fin 2, ‖B q.1 q.2‖
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hB_le : ∀ k j : Fin 2, ‖B k j‖ ≤ S := fun k j =>
        Finset.single_le_sum (f := fun q : Fin 2 × Fin 2 => ‖B q.1 q.2‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ (k, j))
      let Y : H2 := ⟨fun p => ∑ k : Fin 2, X (p.1, k) * B k p.2,
        (Finite.of_fintype (Fin 2 × Fin 2)).memℓp _⟩
      show ‖Y‖ ≤ (4 * S) * ‖X‖
      rw [show (4 * S) * ‖X‖ = 2 * (2 * S * ‖X‖) by ring]
      refine h2_norm_le_of_entry_bound Y (by positivity) fun p => ?_
      change ‖∑ k : Fin 2, X (p.1, k) * B k p.2‖ ≤ 2 * S * ‖X‖
      rw [Fin.sum_univ_two, show 2 * S * ‖X‖ = ‖X‖ * S + ‖X‖ * S by ring]
      calc ‖X (p.1, 0) * B 0 p.2 + X (p.1, 1) * B 1 p.2‖
          ≤ ‖X (p.1, 0)‖ * ‖B 0 p.2‖ + ‖X (p.1, 1)‖ * ‖B 1 p.2‖ := by
            simpa [norm_mul] using norm_add_le (X (p.1, 0) * B 0 p.2) (X (p.1, 1) * B 1 p.2)
        _ ≤ ‖X‖ * S + ‖X‖ * S :=
            add_le_add (mul_le_mul (h2_entry_le_norm X _) (hB_le 0 p.2) (norm_nonneg _) (norm_nonneg _))
              (mul_le_mul (h2_entry_le_norm X _) (hB_le 1 p.2) (norm_nonneg _) (norm_nonneg _)))

@[simp] private theorem leftMul2_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (X : H2)
    (p : Fin 2 × Fin 2) :
    leftMul2 A X p = ∑ k : Fin 2, A p.1 k * X (k, p.2) := rfl

@[simp] private theorem rightMul2_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (X : H2)
    (p : Fin 2 × Fin 2) :
    rightMul2 B X p = ∑ k : Fin 2, X (p.1, k) * B k p.2 := rfl

private theorem leftMul2_one : leftMul2 1 = (1 : H2 →L[ℂ] H2) := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

private theorem rightMul2_one : rightMul2 1 = (1 : H2 →L[ℂ] H2) := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

private theorem leftMul2_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    leftMul2 (A * B) = leftMul2 A * leftMul2 B := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  change (∑ k : Fin 2, (A * B) i k * X (k, j)) = leftMul2 A (leftMul2 B X) (i, j)
  simp only [leftMul2_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem rightMul2_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    rightMul2 (A * B) = rightMul2 B * rightMul2 A := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  change (∑ k : Fin 2, X (i, k) * (A * B) k j) = rightMul2 B (rightMul2 A X) (i, j)
  simp only [rightMul2_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem leftMul2_comm_rightMul2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    leftMul2 A * rightMul2 B = rightMul2 B * leftMul2 A := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  change leftMul2 A (rightMul2 B X) (i, j) = rightMul2 B (leftMul2 A X) (i, j)
  simp only [leftMul2_apply, rightMul2_apply, Fin.sum_univ_two]
  ring

private theorem star_leftMul2 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    star (leftMul2 A) = leftMul2 Aᴴ := by
  refine ContinuousLinearMap.ext fun Y => ext_inner_left ℂ fun X => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_fintype, tsum_fintype]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, leftMul2_apply, Matrix.conjTranspose_apply,
    RCLike.inner_apply, RCLike.star_def, map_add, map_mul]
  ring

private theorem star_rightMul2 (B : Matrix (Fin 2) (Fin 2) ℂ) :
    star (rightMul2 B) = rightMul2 Bᴴ := by
  refine ContinuousLinearMap.ext fun Y => ext_inner_left ℂ fun X => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_fintype, tsum_fintype]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, rightMul2_apply, Matrix.conjTranspose_apply,
    RCLike.inner_apply, RCLike.star_def, map_add, map_mul]
  ring

private def J2 : AntiunitaryInvol H2 where
  toFun X := ⟨fun p => starRingEnd ℂ (X (p.2, p.1)),
    (Finite.of_fintype (Fin 2 × Fin 2)).memℓp _⟩
  invol' X := by ext p; exact Complex.conj_conj _
  map_add' X Y := by ext p; exact map_add _ _ _
  map_smul' c X := by ext p; exact map_mul _ _ _
  inner_map' X Y := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_fintype, tsum_fintype]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, RCLike.inner_apply, Complex.conj_conj]
    ring

@[simp] private theorem J2_apply (X : H2) (p : Fin 2 × Fin 2) :
    J2 X p = starRingEnd ℂ (X (p.2, p.1)) := rfl

private theorem J2_conjOp_leftMul2 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    J2.conjOp (leftMul2 A) = rightMul2 Aᴴ := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  simp only [AntiunitaryInvol.conjOp_apply, J2_apply, leftMul2_apply, rightMul2_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj,
    RCLike.star_def]
  ring

private theorem J2_conjOp_rightMul2 (B : Matrix (Fin 2) (Fin 2) ℂ) :
    J2.conjOp (rightMul2 B) = leftMul2 Bᴴ := by
  refine ContinuousLinearMap.ext fun X => lp.ext <| funext fun ⟨i, j⟩ => ?_
  simp only [AntiunitaryInvol.conjOp_apply, J2_apply, leftMul2_apply, rightMul2_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj,
    RCLike.star_def]
  ring

private def Ω2 : H2 :=
  ⟨fun p => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0,
    (Finite.of_fintype (Fin 2 × Fin 2)).memℓp _⟩

@[simp] private theorem Ω2_apply (p : Fin 2 × Fin 2) :
    Ω2 p = if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := rfl

private theorem leftMul2_Ω2 (A : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 2 × Fin 2) :
    leftMul2 A Ω2 p = ((1 / Real.sqrt 2 : ℝ) : ℂ) * A p.1 p.2 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, mul_comm]

private theorem rightMul2_Ω2 (B : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 2 × Fin 2) :
    rightMul2 B Ω2 p = ((1 / Real.sqrt 2 : ℝ) : ℂ) * B p.1 p.2 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

private def E2 (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r s => if r = i ∧ s = j then 1 else 0

private theorem sqrt2_mul_inv_sqrt2 :
    ((Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
  exact_mod_cast mul_one_div_cancel hs

private theorem single_eq_rightMul2_Ω2 (i j : Fin 2) :
    lp.single (E := fun _ : Fin 2 × Fin 2 => ℂ) 2 (i, j) 1 =
      ((Real.sqrt 2 : ℝ) : ℂ) • rightMul2 (E2 i j) Ω2 := by
  ext ⟨r, s⟩
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, rightMul2_Ω2, E2, Matrix.of_apply,
    lp.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs with h1 h2
  · rw [← mul_assoc, sqrt2_mul_inv_sqrt2, one_mul]
  · exfalso; exact h2 ⟨h1.1.symm, h1.2.symm⟩
  · exfalso; exact h1 ⟨h2.1.symm, h2.2.symm⟩
  · simp

private theorem single_eq_leftMul2_Ω2 (i j : Fin 2) :
    lp.single (E := fun _ : Fin 2 × Fin 2 => ℂ) 2 (i, j) 1 =
      ((Real.sqrt 2 : ℝ) : ℂ) • leftMul2 (E2 i j) Ω2 := by
  ext ⟨r, s⟩
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, leftMul2_Ω2, E2, Matrix.of_apply,
    lp.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs with h1 h2
  · rw [← mul_assoc, sqrt2_mul_inv_sqrt2, one_mul]
  · exfalso; exact h2 ⟨h1.1.symm, h1.2.symm⟩
  · exfalso; exact h1 ⟨h2.1.symm, h2.2.symm⟩
  · simp

private theorem h2_eq_sum_single (X : H2) :
    X = ∑ p : Fin 2 × Fin 2, X p • lp.single (E := fun _ : Fin 2 × Fin 2 => ℂ) 2 p 1 := by
  ext q
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hpq; simp [hpq.symm]
  · intro h; exact absurd (Finset.mem_univ q) h

/-- The type `I₂` factor of left `2 × 2` matrix multiplications on `H2`. -/
private def mat2VN : VonNeumannAlgebra H2 where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range rightMul2)
  centralizer_centralizer' := by
    have hcoe : (StarSubalgebra.centralizer ℂ (Set.range rightMul2) : Set (H2 →L[ℂ] H2)) =
        Set.centralizer (Set.range rightMul2) := by
      ext T
      rw [SetLike.mem_coe, StarSubalgebra.mem_centralizer_iff]
      refine ⟨fun h S hS => (h S hS).1, fun h S hS => ?_⟩
      rcases hS with ⟨B, rfl⟩
      refine ⟨h _ ⟨B, rfl⟩, ?_⟩
      rw [star_rightMul2]
      exact h _ ⟨Bᴴ, rfl⟩
    change (StarSubalgebra.centralizer ℂ (Set.range rightMul2) :
        Set (H2 →L[ℂ] H2)).centralizer.centralizer =
      (StarSubalgebra.centralizer ℂ (Set.range rightMul2) : Set (H2 →L[ℂ] H2))
    rw [hcoe]
    ext T
    refine ⟨fun hT S hS => ?_, fun hT S hS => (hS T hT).symm⟩
    exact hT S fun U hU => (hU S hS).symm

private theorem mem_mat2VN_iff (T : H2 →L[ℂ] H2) :
    T ∈ mat2VN ↔ ∀ B : Matrix (Fin 2) (Fin 2) ℂ, rightMul2 B * T = T * rightMul2 B := by
  change T ∈ StarSubalgebra.centralizer ℂ (Set.range rightMul2) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  refine ⟨fun h B => (h _ ⟨B, rfl⟩).1, fun h S hS => ?_⟩
  rcases hS with ⟨B, rfl⟩
  refine ⟨h B, ?_⟩
  rw [star_rightMul2]
  exact h Bᴴ

private theorem leftMul2_mem_mat2VN (A : Matrix (Fin 2) (Fin 2) ℂ) : leftMul2 A ∈ mat2VN :=
  (mem_mat2VN_iff _).mpr fun B => (leftMul2_comm_rightMul2 A B).symm

private theorem mat2VN_separating (T : H2 →L[ℂ] H2) (hT : T ∈ mat2VN) (h0 : T Ω2 = 0) :
    T = 0 := by
  have hsingle : ∀ p : Fin 2 × Fin 2,
      T (lp.single (E := fun _ : Fin 2 × Fin 2 => ℂ) 2 p 1) = 0 := fun ⟨i, j⟩ => by
    have hcomm := (mem_mat2VN_iff T).mp hT (E2 i j)
    have happ : rightMul2 (E2 i j) (T Ω2) = T (rightMul2 (E2 i j) Ω2) :=
      congr_arg (fun S : H2 →L[ℂ] H2 => S Ω2) hcomm
    rw [h0, map_zero] at happ
    rw [single_eq_rightMul2_Ω2 i j, map_smul, ← happ, smul_zero]
  ext X
  rw [h2_eq_sum_single X, map_sum]
  simp [hsingle]

private theorem eq_leftMul2_of_mem_mat2VN {T : H2 →L[ℂ] H2} (hT : T ∈ mat2VN) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, T = leftMul2 A := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => ((Real.sqrt 2 : ℝ) : ℂ) * T Ω2 (i, j)
  refine ⟨A, sub_eq_zero.mp (mat2VN_separating _ (sub_mem hT (leftMul2_mem_mat2VN A)) ?_)⟩
  ext ⟨i, j⟩
  simp only [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, leftMul2_Ω2, A,
    Matrix.of_apply, lp.coeFn_zero, Pi.zero_apply]
  rw [← mul_assoc, mul_comm ((1 / Real.sqrt 2 : ℝ) : ℂ), sqrt2_mul_inv_sqrt2, one_mul, sub_self]

private theorem rightMul2_mem_commutant (B : Matrix (Fin 2) (Fin 2) ℂ) :
    rightMul2 B ∈ mat2VN.commutant := by
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro T hT
  exact ((mem_mat2VN_iff T).mp hT B).symm

private theorem eq_rightMul2_of_mem_commutant {T : H2 →L[ℂ] H2} (hT : T ∈ mat2VN.commutant) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℂ, T = rightMul2 B := by
  have hsep : ∀ S ∈ mat2VN.commutant, S Ω2 = 0 → S = 0 := fun S hS h0 => by
    have hsingle : ∀ p : Fin 2 × Fin 2,
        S (lp.single (E := fun _ : Fin 2 × Fin 2 => ℂ) 2 p 1) = 0 := fun ⟨i, j⟩ => by
      have hcomm := (VonNeumannAlgebra.mem_commutant_iff.mp hS) (leftMul2 (E2 i j))
        (leftMul2_mem_mat2VN _)
      have happ : S (leftMul2 (E2 i j) Ω2) = leftMul2 (E2 i j) (S Ω2) :=
        congr_arg (fun U : H2 →L[ℂ] H2 => U Ω2) hcomm
      rw [h0, map_zero] at happ
      rw [single_eq_leftMul2_Ω2 i j, map_smul, happ, smul_zero]
    ext X
    rw [h2_eq_sum_single X, map_sum]
    simp [hsingle]
  let B : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => ((Real.sqrt 2 : ℝ) : ℂ) * T Ω2 (i, j)
  refine ⟨B, sub_eq_zero.mp (hsep _ (sub_mem hT (rightMul2_mem_commutant B)) ?_)⟩
  ext ⟨i, j⟩
  simp only [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, rightMul2_Ω2, B,
    Matrix.of_apply, lp.coeFn_zero, Pi.zero_apply]
  rw [← mul_assoc, mul_comm ((1 / Real.sqrt 2 : ℝ) : ℂ), sqrt2_mul_inv_sqrt2, one_mul, sub_self]

private def mat2StandardForm : StandardForm mat2VN where
  Ω := Ω2
  separating := mat2VN_separating
  cyclic := fun X => by
    let A : Matrix (Fin 2) (Fin 2) ℂ :=
      Matrix.of fun i j => ((Real.sqrt 2 : ℝ) : ℂ) * X (i, j)
    refine subset_closure ⟨⟨leftMul2 A, leftMul2_mem_mat2VN A⟩, ?_⟩
    ext ⟨i, j⟩
    change leftMul2 A Ω2 (i, j) = X (i, j)
    rw [leftMul2_Ω2]
    dsimp [A]
    rw [← mul_assoc, mul_comm ((1 / Real.sqrt 2 : ℝ) : ℂ), sqrt2_mul_inv_sqrt2, one_mul]
  J := J2
  J_omega := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp
  conj_mem_commutant_iff := fun T => by
    constructor
    · intro hJT
      obtain ⟨B, hB⟩ := eq_rightMul2_of_mem_commutant hJT
      have hT : T = J2.conjOp (rightMul2 B) := by rw [← hB, J2.conjOp_invol]
      rw [hT, J2_conjOp_rightMul2]
      exact leftMul2_mem_mat2VN Bᴴ
    · intro hT
      obtain ⟨A, rfl⟩ := eq_leftMul2_of_mem_mat2VN hT
      rw [J2_conjOp_leftMul2]
      exact rightMul2_mem_commutant Aᴴ
  natural_cone_pos := fun T hT => by
    obtain ⟨A, rfl⟩ := eq_leftMul2_of_mem_mat2VN hT
    rw [J2_conjOp_leftMul2]
    have hΩeq : rightMul2 Aᴴ Ω2 = leftMul2 Aᴴ Ω2 := by
      ext p; rw [rightMul2_Ω2, leftMul2_Ω2]
    rw [hΩeq]
    have hadj : inner ℂ Ω2 (leftMul2 A (leftMul2 Aᴴ Ω2)) =
        inner ℂ (leftMul2 Aᴴ Ω2) (leftMul2 Aᴴ Ω2) := by
      calc inner ℂ Ω2 (leftMul2 A (leftMul2 Aᴴ Ω2))
          = inner ℂ (ContinuousLinearMap.adjoint (leftMul2 A) Ω2) (leftMul2 Aᴴ Ω2) :=
            (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
        _ = inner ℂ ((star (leftMul2 A)) Ω2) (leftMul2 Aᴴ Ω2) := by
            rw [← ContinuousLinearMap.star_eq_adjoint]
        _ = inner ℂ (leftMul2 Aᴴ Ω2) (leftMul2 Aᴴ Ω2) := by rw [star_leftMul2]
    rw [hadj, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg _

/-- 2-adic valuation parity character `n ↦ (-1)^{v₂(n)}` on `ℕ+`. -/
private def chi2 (n : ℕ+) : ℂ := (-1 : ℂ) ^ ((n : ℕ).factorization 2)

private theorem chi2_one : chi2 1 = 1 := by simp [chi2]

private theorem chi2_two : chi2 2 = -1 := by
  change (-1 : ℂ) ^ ((2 : ℕ).factorization 2) = -1
  rw [Nat.Prime.factorization_self Nat.prime_two, pow_one]

private theorem chi2_mul (m n : ℕ+) : chi2 (m * n) = chi2 m * chi2 n := by
  simp only [chi2, PNat.mul_coe, Nat.factorization_mul m.ne_zero n.ne_zero, Finsupp.add_apply,
    pow_add]

private theorem chi2_sq (n : ℕ+) : chi2 n * chi2 n = 1 := by
  simp only [chi2, ← mul_pow]
  norm_num

private theorem chi2_conj (n : ℕ+) : starRingEnd ℂ (chi2 n) = chi2 n := by
  simp [chi2]

private def D2 (n : ℕ+) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, chi2 n]

private theorem D2_one : D2 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D2, chi2_one]

private theorem D2_mul (m n : ℕ+) : D2 (m * n) = D2 m * D2 n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D2, Matrix.mul_apply, Fin.sum_univ_two, chi2_mul]

private theorem D2_conjTranspose (n : ℕ+) : (D2 n)ᴴ = D2 n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D2, Matrix.conjTranspose_apply, RCLike.star_def, chi2_conj]

private theorem D2_sq (n : ℕ+) : D2 n * D2 n = 1 := by
  rw [← D2_mul, chi2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D2, chi2_mul, chi2_sq]

/-- **Nontrivial noncommutative `StandardForm` realization of a Hecke-isometric partner kernel.**
On `M₂(ℂ)` in tracial standard form, 2-adic parity conjugation `U(n) X = D(n) X D(n)` fixes `Ω`,
satisfies `J U(n) J = U(n)*`, escapes both `M` and `M'`, preserves `M` under `covShift`, and
induces the nonconstant Hecke-dilation invariant natural-cone kernel `K(m, n) = (1 + χ₂(m n)) / 2`. -/
theorem exists_nontrivial_vacuumFixing_partner_standardForm_heckeInv :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (M : VonNeumannAlgebra H) (ms : StandardForm M)
      (U : ℕ+ → H →L[ℂ] H) (A₀ : H →L[ℂ] H),
      U 1 = 1 ∧
      (∀ m n : ℕ+, U (m * n) = U m * U n) ∧
      (∀ n : ℕ+, star (U n) * U n = 1 ∧ U n * star (U n) = 1) ∧
      (∀ n : ℕ+, U n ms.Ω = ms.Ω) ∧
      (∀ n : ℕ+, ms.J.conjOp (U n) = star (U n)) ∧
      U 2 ∉ M ∧ U 2 ∉ M.commutant ∧
      A₀ ∈ M ∧ (∀ n : ℕ+, covShift U n A₀ ∈ M) ∧
      let K : ℕ+ → ℕ+ → ℝ := fun m n =>
        (inner ℂ ms.Ω (covShift U m A₀ (ms.J.conjOp (covShift U n A₀) ms.Ω))).re
      IsMulHankel K ∧ IsHeckeDilationInv K ∧ K 1 1 = 1 ∧ K 1 2 = 0 := by
  let U : ℕ+ → H2 →L[ℂ] H2 := fun n => leftMul2 (D2 n) * rightMul2 (D2 n)
  let M₀ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 0]
  let A₀ : H2 →L[ℂ] H2 := leftMul2 M₀
  have hU1 : U 1 = 1 := by
    simp only [U, D2_one, leftMul2_one, rightMul2_one, mul_one]
  have hUmul : ∀ m n : ℕ+, U (m * n) = U m * U n := fun m n => by
    have hDcomm : D2 n * D2 m = D2 m * D2 n := by rw [← D2_mul, ← D2_mul, mul_comm]
    calc leftMul2 (D2 (m * n)) * rightMul2 (D2 (m * n))
        = leftMul2 (D2 m * D2 n) * rightMul2 (D2 n * D2 m) := by rw [D2_mul, hDcomm]
      _ = (leftMul2 (D2 m) * leftMul2 (D2 n)) * (rightMul2 (D2 m) * rightMul2 (D2 n)) := by
          rw [leftMul2_mul, rightMul2_mul]
      _ = leftMul2 (D2 m) * (leftMul2 (D2 n) * rightMul2 (D2 m)) * rightMul2 (D2 n) := by
          simp only [mul_assoc]
      _ = leftMul2 (D2 m) * (rightMul2 (D2 m) * leftMul2 (D2 n)) * rightMul2 (D2 n) := by
          rw [leftMul2_comm_rightMul2]
      _ = U m * U n := by simp only [U, mul_assoc]
  have hU_sa : ∀ n : ℕ+, star (U n) = U n := fun n => by
    simp only [U, star_mul, star_leftMul2, star_rightMul2, D2_conjTranspose]
    exact (leftMul2_comm_rightMul2 (D2 n) (D2 n)).symm
  have hU_sq : ∀ n : ℕ+, U n * U n = 1 := fun n => by
    rw [← hUmul]
    have h1 : D2 (n * n) = 1 := by rw [D2_mul, D2_sq]
    simp only [U, h1, leftMul2_one, rightMul2_one, mul_one]
  have hU_unit : ∀ n : ℕ+, star (U n) * U n = 1 ∧ U n * star (U n) = 1 := fun n => by
    rw [hU_sa]; exact ⟨hU_sq n, hU_sq n⟩
  have hUΩ : ∀ n : ℕ+, U n Ω2 = Ω2 := fun n => by
    change leftMul2 (D2 n) (rightMul2 (D2 n) Ω2) = Ω2
    have heq : rightMul2 (D2 n) Ω2 = leftMul2 (D2 n) Ω2 := by
      ext p; rw [rightMul2_Ω2, leftMul2_Ω2]
    rw [heq]
    change (leftMul2 (D2 n) * leftMul2 (D2 n)) Ω2 = Ω2
    rw [← leftMul2_mul, D2_sq, leftMul2_one]
    rfl
  have hUJ : ∀ n : ℕ+, J2.conjOp (U n) = star (U n) := fun n => by
    rw [hU_sa]
    simp only [U, AntiunitaryInvol.conjOp_mul, J2_conjOp_leftMul2, J2_conjOp_rightMul2,
      D2_conjTranspose]
    exact (leftMul2_comm_rightMul2 (D2 n) (D2 n)).symm
  have hU2_ne1 : U 2 ≠ 1 := by
    intro h1
    let e01 : H2 := lp.single 2 (0, 1) 1
    have happ : U 2 e01 (0, 1) = (1 : H2 →L[ℂ] H2) e01 (0, 1) :=
      congr_arg (fun T : H2 →L[ℂ] H2 => T e01 (0, 1)) h1
    have hlhs : U 2 e01 (0, 1) = -1 := by
      change leftMul2 (D2 2) (rightMul2 (D2 2) e01) (0, 1) = -1
      simp only [leftMul2_apply, rightMul2_apply, Fin.sum_univ_two, D2, e01, lp.single_apply,
        Pi.single_apply, chi2_two]
      norm_num
    have hrhs : (1 : H2 →L[ℂ] H2) e01 (0, 1) = 1 := by
      simp [e01, lp.single_apply]
    rw [hlhs, hrhs] at happ
    norm_num at happ
  have hU2_notM : U 2 ∉ mat2VN := by
    intro hmem
    refine hU2_ne1 (sub_eq_zero.mp (mat2VN_separating (U 2 - 1) (sub_mem hmem mat2VN.one_mem) ?_))
    simp [hUΩ 2]
  have hU2_notComm : U 2 ∉ mat2VN.commutant := by
    intro hcomm
    have hJmem : J2.conjOp (U 2) ∈ mat2VN :=
      (mat2StandardForm.conjOp_mem_iff_mem_commutant (U 2)).mpr hcomm
    rw [hUJ 2, hU_sa 2] at hJmem
    exact hU2_notM hJmem
  have hcov : ∀ n : ℕ+, covShift U n A₀ = leftMul2 !![1, chi2 n; 0, 0] := fun n => by
    have hmulD : D2 n * M₀ * D2 n = !![1, chi2 n; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [D2, M₀, Matrix.mul_apply, Fin.sum_univ_two]
    calc covShift U n A₀
        = (leftMul2 (D2 n) * rightMul2 (D2 n)) * leftMul2 M₀ *
            (leftMul2 (D2 n) * rightMul2 (D2 n)) := by rw [covShift, hU_sa]
      _ = leftMul2 (D2 n) * leftMul2 M₀ * leftMul2 (D2 n) *
            (rightMul2 (D2 n) * rightMul2 (D2 n)) := by
            simp only [mul_assoc]
            congr 1
            rw [← mul_assoc (rightMul2 (D2 n)), ← leftMul2_comm_rightMul2,
              mul_assoc (leftMul2 M₀), ← mul_assoc (rightMul2 (D2 n)),
              ← leftMul2_comm_rightMul2, mul_assoc]
      _ = leftMul2 (D2 n * M₀ * D2 n) * rightMul2 (D2 n * D2 n) := by
            rw [← leftMul2_mul, ← leftMul2_mul, ← rightMul2_mul]
      _ = leftMul2 !![1, chi2 n; 0, 0] := by rw [hmulD, D2_sq, rightMul2_one, mul_one]
  refine ⟨H2, inferInstance, inferInstance, inferInstance, mat2VN, mat2StandardForm, U, A₀,
    hU1, hUmul, hU_unit, hUΩ, hUJ, hU2_notM, hU2_notComm, leftMul2_mem_mat2VN M₀,
    fun n => by rw [hcov n]; exact leftMul2_mem_mat2VN _, ?_⟩
  intro K
  have hK_val : ∀ m n : ℕ+, K m n = (1 + (chi2 (m * n)).re) / 2 := fun m n => by
    change (inner ℂ Ω2 (covShift U m A₀ (J2.conjOp (covShift U n A₀) Ω2))).re = _
    rw [hcov m, hcov n, J2_conjOp_leftMul2]
    set Bm : Matrix (Fin 2) (Fin 2) ℂ := !![1, chi2 m; 0, 0]
    set Bn : Matrix (Fin 2) (Fin 2) ℂ := !![1, chi2 n; 0, 0]
    have hΩeq : rightMul2 Bnᴴ Ω2 = leftMul2 Bnᴴ Ω2 := by ext p; rw [rightMul2_Ω2, leftMul2_Ω2]
    rw [hΩeq]
    have hadj : inner ℂ Ω2 (leftMul2 Bm (leftMul2 Bnᴴ Ω2)) =
        inner ℂ (leftMul2 Bmᴴ Ω2) (leftMul2 Bnᴴ Ω2) := by
      calc inner ℂ Ω2 (leftMul2 Bm (leftMul2 Bnᴴ Ω2))
          = inner ℂ (ContinuousLinearMap.adjoint (leftMul2 Bm) Ω2) (leftMul2 Bnᴴ Ω2) :=
            (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
        _ = inner ℂ ((star (leftMul2 Bm)) Ω2) (leftMul2 Bnᴴ Ω2) := by
            rw [← ContinuousLinearMap.star_eq_adjoint]
        _ = inner ℂ (leftMul2 Bmᴴ Ω2) (leftMul2 Bnᴴ Ω2) := by rw [star_leftMul2]
    have hsq2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
      have hs : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = 1 / 2 := by
        rw [one_div_mul_one_div, Real.mul_self_sqrt zero_le_two]
      exact_mod_cast hs
    rw [hadj, lp.inner_eq_tsum, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [leftMul2_Ω2, Matrix.conjTranspose_apply, Bm, Bn, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, RCLike.inner_apply,
      RCLike.star_def, chi2_conj, map_mul, Complex.conj_ofReal, mul_zero, add_zero]
    have hcomb : (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1) * (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1) +
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * chi2 n) * (((1 / Real.sqrt 2 : ℝ) : ℂ) * chi2 m) =
        (1 / 2 : ℂ) * (1 + chi2 (m * n)) := by
      rw [chi2_mul]
      linear_combination (1 + chi2 m * chi2 n) * hsq2
    rw [hcomb]
    simp only [one_div, Complex.mul_re, Complex.inv_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_re, Complex.one_re]
    ring
  have hsq_class : ∀ p k : ℕ+,
      (1 + (chi2 (p ^ 2 * k)).re) / 2 = (1 + (chi2 k).re) / 2 := fun p k => by
    rw [sq, mul_assoc, chi2_mul, ← mul_assoc, ← chi2_mul, show chi2 (p * p) = 1 by
      rw [chi2_mul, chi2_sq], one_mul]
  obtain ⟨hHankel, hHecke⟩ := (isMulHankel_and_heckeInv_iff_sqClass K).mpr
    ⟨fun k => (1 + (chi2 k).re) / 2, hsq_class, hK_val⟩
  refine ⟨hHankel, hHecke, ?_, ?_⟩
  · rw [hK_val, one_mul, chi2_one]; norm_num
  · rw [hK_val, one_mul, chi2_two]; norm_num

end Mat2Realization

/-! ### 3. Borchers `ax + b` spectral and Bohr-frequency rigidity -/

/-- A strongly continuous unitary Borchers pair `(Δ, U)` on a complex Hilbert space satisfying the
half-sided modular scaling relation `Δ(s) U(a) Δ(-s) = U(e^{-2πs} a)`. -/
structure BorchersPair (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  U : ℝ → H →L[ℂ] H
  U_zero : U 0 = 1
  U_add : ∀ a b : ℝ, U (a + b) = U a * U b
  U_iso : ∀ a : ℝ, star (U a) * U a = 1
  U_cont : ∀ x : H, Continuous fun a : ℝ => U a x
  Δ : ℝ → H →L[ℂ] H
  Δ_zero : Δ 0 = 1
  Δ_add : ∀ s t : ℝ, Δ (s + t) = Δ s * Δ t
  Δ_iso : ∀ s : ℝ, star (Δ s) * Δ s = 1
  Δ_cont : ∀ x : H, Continuous fun s : ℝ => Δ s x
  borchers : ∀ s a : ℝ, Δ s * U a * Δ (-s) = U (Real.exp (-2 * Real.pi * s) * a)

namespace BorchersPair

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem U_mul_neg (B : BorchersPair H) (a : ℝ) : B.U a * B.U (-a) = 1 := by
  rw [← B.U_add, add_neg_cancel, B.U_zero]

theorem U_neg_mul (B : BorchersPair H) (a : ℝ) : B.U (-a) * B.U a = 1 := by
  rw [← B.U_add, neg_add_cancel, B.U_zero]

theorem star_U [CompleteSpace H] (B : BorchersPair H) (a : ℝ) : star (B.U a) = B.U (-a) := by
  calc star (B.U a) = star (B.U a) * (B.U a * B.U (-a)) := by rw [B.U_mul_neg, mul_one]
    _ = (star (B.U a) * B.U a) * B.U (-a) := (mul_assoc _ _ _).symm
    _ = B.U (-a) := by rw [B.U_iso, one_mul]

theorem U_mul_star [CompleteSpace H] (B : BorchersPair H) (a : ℝ) :
    B.U a * star (B.U a) = 1 := by
  rw [B.star_U, B.U_mul_neg]

theorem Δ_mul_neg (B : BorchersPair H) (s : ℝ) : B.Δ s * B.Δ (-s) = 1 := by
  rw [← B.Δ_add, add_neg_cancel, B.Δ_zero]

theorem Δ_neg_mul (B : BorchersPair H) (s : ℝ) : B.Δ (-s) * B.Δ s = 1 := by
  rw [← B.Δ_add, neg_add_cancel, B.Δ_zero]

theorem inner_U [CompleteSpace H] (B : BorchersPair H) (a : ℝ) (x y : H) :
    inner ℂ (B.U a x) (B.U a y) = inner ℂ x y := by
  calc inner ℂ (B.U a x) (B.U a y)
      = inner ℂ x (ContinuousLinearMap.adjoint (B.U a) (B.U a y)) :=
        ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner ℂ x ((star (B.U a) * B.U a) y) := by
        rw [← ContinuousLinearMap.star_eq_adjoint]; rfl
    _ = inner ℂ x y := by rw [B.U_iso]; rfl

theorem norm_U [CompleteSpace H] (B : BorchersPair H) (a : ℝ) (x : H) :
    ‖B.U a x‖ = ‖x‖ := by
  have hsq : ‖B.U a x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), B.inner_U]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

theorem norm_Δ [CompleteSpace H] (B : BorchersPair H) (s : ℝ) (x : H) :
    ‖B.Δ s x‖ = ‖x‖ := by
  have hinner : inner ℂ (B.Δ s x) (B.Δ s x) = inner ℂ x x := by
    calc inner ℂ (B.Δ s x) (B.Δ s x)
        = inner ℂ x (ContinuousLinearMap.adjoint (B.Δ s) (B.Δ s x)) :=
          ContinuousLinearMap.adjoint_inner_right _ _ _
      _ = inner ℂ x ((star (B.Δ s) * B.Δ s) x) := by
          rw [← ContinuousLinearMap.star_eq_adjoint]; rfl
      _ = inner ℂ x x := by rw [B.Δ_iso]; rfl
  have hsq : ‖B.Δ s x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- **Forced vacuum invariance.** Any vector fixed by the modular flow `Δ` is automatically fixed
by the entire translation group `U`. -/
theorem fix_of_delta_fix [CompleteSpace H] (B : BorchersPair H) {Ω : H}
    (hΔ : ∀ s : ℝ, B.Δ s Ω = Ω) (a : ℝ) : B.U a Ω = Ω := by
  have hnorm_eq : ∀ s : ℝ, ‖B.U a Ω - Ω‖ = ‖B.U (Real.exp (-2 * Real.pi * s) * a) Ω - Ω‖ := by
    intro s
    calc ‖B.U a Ω - Ω‖ = ‖B.Δ s (B.U a Ω - Ω)‖ := (B.norm_Δ s _).symm
      _ = ‖B.Δ s (B.U a (B.Δ (-s) Ω)) - Ω‖ := by rw [map_sub, hΔ (-s), hΔ s]
      _ = ‖(B.Δ s * B.U a * B.Δ (-s)) Ω - Ω‖ := rfl
      _ = ‖B.U (Real.exp (-2 * Real.pi * s) * a) Ω - Ω‖ := by rw [B.borchers]
  have htend_arg : Tendsto (fun s : ℝ => Real.exp (-2 * Real.pi * s) * a) atTop (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => -2 * Real.pi * s) atTop atBot :=
      Tendsto.neg_const_mul_atTop (by linarith [Real.pi_pos]) tendsto_id
    simpa only [zero_mul] using (Real.tendsto_exp_atBot.comp hlin).mul_const a
  have htend_norm : Tendsto (fun s : ℝ => ‖B.U (Real.exp (-2 * Real.pi * s) * a) Ω - Ω‖)
      atTop (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => ‖B.U t Ω - Ω‖) :=
      ((B.U_cont Ω).sub continuous_const).norm
    have h0 : ‖B.U 0 Ω - Ω‖ = 0 := by simp [B.U_zero]
    simpa only [Function.comp_def, h0] using hcont.continuousAt.tendsto.comp htend_arg
  simp_rw [← hnorm_eq] at htend_norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds htend_norm))

/-- **Strict externality.** In any standard-form von Neumann algebra `(H, M, ms)` whose vector
`ms.Ω` is fixed by `B.Δ`, `B.U a` lies in `M` (or in `M'`) if and only if `B.U a = 1`. -/
theorem mem_iff_eq_one [CompleteSpace H] (B : BorchersPair H) {M : VonNeumannAlgebra H}
    (ms : StandardForm M) (hΔ : ∀ s : ℝ, B.Δ s ms.Ω = ms.Ω) (a : ℝ) :
    (B.U a ∈ M ↔ B.U a = 1) ∧ (B.U a ∈ M.commutant ↔ B.U a = 1) := by
  have hUΩ : B.U a ms.Ω = ms.Ω := B.fix_of_delta_fix hΔ a
  have hM : B.U a ∈ M ↔ B.U a = 1 :=
    ⟨fun h => sub_eq_zero.mp (ms.separating _ (sub_mem h M.one_mem) (by simp [hUΩ])),
      fun h => h ▸ M.one_mem⟩
  refine ⟨hM, ⟨fun hc => ?_, fun h => h ▸ M.commutant.one_mem⟩⟩
  have hJM : ms.J.conjOp (B.U a) ∈ M := (ms.conjOp_mem_iff_mem_commutant _).mpr hc
  have hJ1 : ms.J.conjOp (B.U a) = 1 :=
    sub_eq_zero.mp (ms.separating _ (sub_mem hJM M.one_mem)
      (by simp [ms.J_omega, hUΩ]))
  calc B.U a = ms.J.conjOp (ms.J.conjOp (B.U a)) := (ms.J.conjOp_invol _).symm
    _ = 1 := by rw [hJ1, AntiunitaryInvol.conjOp_one]

/-- **Absence of nonzero continuous eigenmodes.** In any `BorchersPair`, a vector `v` satisfying
`U(t) v = e^{i ω t} v` for all `t ∈ ℝ` with `ω ≠ 0` vanishes identically. -/
theorem eigenmode_eq_zero [CompleteSpace H] (B : BorchersPair H) {ω : ℝ} (hω : ω ≠ 0) {v : H}
    (hv : ∀ t : ℝ, B.U t v = Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) • v) :
    v = 0 := by
  have hcomm_v : ∀ (s t : ℝ),
      B.U t (B.Δ (-s) v) =
        Complex.exp (Complex.I * ((Real.exp (-2 * Real.pi * s) * ω : ℝ) : ℂ) * (t : ℂ)) •
          (B.Δ (-s) v) := fun s t => by
    have hrel : B.U t * B.Δ (-s) = B.Δ (-s) * B.U (Real.exp (-2 * Real.pi * s) * t) := by
      calc B.U t * B.Δ (-s)
          = (B.Δ (-s) * B.Δ s) * B.U t * B.Δ (-s) := by rw [B.Δ_neg_mul, one_mul]
        _ = B.Δ (-s) * (B.Δ s * B.U t * B.Δ (-s)) := by simp only [mul_assoc]
        _ = B.Δ (-s) * B.U (Real.exp (-2 * Real.pi * s) * t) := by rw [B.borchers]
    calc B.U t (B.Δ (-s) v) = (B.U t * B.Δ (-s)) v := rfl
      _ = B.Δ (-s) (B.U (Real.exp (-2 * Real.pi * s) * t) v) := by rw [hrel]; rfl
      _ = B.Δ (-s) (Complex.exp (Complex.I * (ω : ℂ) *
            ((Real.exp (-2 * Real.pi * s) * t : ℝ) : ℂ)) • v) := by rw [hv]
      _ = Complex.exp (Complex.I * ((Real.exp (-2 * Real.pi * s) * ω : ℝ) : ℂ) * (t : ℂ)) •
            (B.Δ (-s) v) := by
          rw [map_smul]
          congr 2
          push_cast
          ring
  have horth : ∀ {s : ℝ}, s ≠ 0 → inner ℂ v (B.Δ (-s) v) = 0 := fun {s} hs => by
    have hexp_ne : Real.exp (-2 * Real.pi * s) ≠ 1 := by
      rw [Ne, Real.exp_eq_one_iff]
      exact mul_ne_zero (by linarith [Real.pi_pos]) hs
    set d : ℝ := (1 - Real.exp (-2 * Real.pi * s)) * ω
    have hd : d ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hexp_ne.symm) hω
    set t₀ : ℝ := Real.pi / d
    have hunit := (B.inner_U t₀ v (B.Δ (-s) v)).symm
    rw [hv t₀, hcomm_v s t₀, inner_smul_left, inner_smul_right, ← mul_assoc] at hunit
    have hphase : starRingEnd ℂ (Complex.exp (Complex.I * (ω : ℂ) * (t₀ : ℂ))) *
        Complex.exp (Complex.I * ((Real.exp (-2 * Real.pi * s) * ω : ℝ) : ℂ) * (t₀ : ℂ)) = -1 := by
      rw [← Complex.exp_conj]
      have hconj : starRingEnd ℂ (Complex.I * (ω : ℂ) * (t₀ : ℂ)) =
          -Complex.I * (ω : ℂ) * (t₀ : ℂ) := by
        simp only [map_mul, conj_I, Complex.conj_ofReal, neg_mul]
      rw [hconj, ← Complex.exp_add]
      have harg : -Complex.I * (ω : ℂ) * (t₀ : ℂ) +
          Complex.I * ((Real.exp (-2 * Real.pi * s) * ω : ℝ) : ℂ) * (t₀ : ℂ) =
          -(Real.pi * Complex.I) := by
        have hdt : d * t₀ = Real.pi := mul_div_cancel₀ Real.pi hd
        have hc : -Complex.I * (ω : ℂ) * (t₀ : ℂ) +
            Complex.I * ((Real.exp (-2 * Real.pi * s) * ω : ℝ) : ℂ) * (t₀ : ℂ) =
            -(((d * t₀ : ℝ) : ℂ) * Complex.I) := by
          simp only [d]; push_cast; ring
        rw [hc, hdt]
        push_cast
        rfl
      rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    rw [hphase, neg_one_mul] at hunit
    linear_combination (1 / 2 : ℂ) * hunit
  have hcont : Continuous (fun s : ℝ => inner ℂ v (B.Δ (-s) v)) :=
    continuous_const.inner ((B.Δ_cont v).comp continuous_neg)
  have htend_arg : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htend_val : Tendsto (fun n : ℕ => inner ℂ v (B.Δ (-((1 : ℝ) / ((n : ℝ) + 1))) v))
      atTop (𝓝 (inner ℂ v (B.Δ (-0) v))) :=
    hcont.continuousAt.tendsto.comp htend_arg
  have hzero_seq : ∀ n : ℕ, inner ℂ v (B.Δ (-((1 : ℝ) / ((n : ℝ) + 1))) v) = 0 := fun n =>
    horth (by positivity)
  simp_rw [hzero_seq, neg_zero, B.Δ_zero] at htend_val
  exact inner_self_eq_zero.mp (tendsto_nhds_unique htend_val tendsto_const_nhds)

private def innerRightCLM (w : H) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun y => inner ℂ w y
      map_add' := fun x y => inner_add_right w x y
      map_smul' := fun c y => inner_smul_right w y c }
    ‖w‖
    (fun y => norm_inner_le_norm w y)

@[simp] private theorem innerRightCLM_apply (w y : H) : innerRightCLM w y = inner ℂ w y := rfl

private theorem eigenvector_eq_zero_of_pos [CompleteSpace H] (B : BorchersPair H)
    {a : ℝ} (ha : 0 < a) {μ : ℂ} (hnorm : ‖μ‖ = 1) (hμ : μ ≠ 1) {w : H} (hw : B.U a w = μ • w) :
    w = 0 := by
  set θ : ℝ := Complex.arg μ
  have hμ_exp : Complex.exp ((θ : ℂ) * Complex.I) = μ := by
    have h := Complex.norm_mul_exp_arg_mul_I μ
    rwa [hnorm, Complex.ofReal_one, one_mul] at h
  have hθ_ne : θ ≠ 0 := by
    intro h0
    apply hμ
    rw [← hμ_exp, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  let ω : ℤ → ℝ := fun k => (θ + 2 * Real.pi * (k : ℝ)) / a
  have hω_ne : ∀ k : ℤ, ω k ≠ 0 := fun k => by
    refine div_ne_zero ?_ ha.ne'
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
      have hle := Complex.arg_le_pi μ
      linarith [Real.pi_pos]
    · simpa using hθ_ne
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hgt := Complex.neg_pi_lt_arg μ
      linarith [Real.pi_pos]
  let F : ℤ → ℝ → H := fun k t => Complex.exp (-Complex.I * (ω k : ℂ) * (t : ℂ)) • B.U t w
  have hF_cont : ∀ k : ℤ, Continuous (F k) := fun k => by
    refine Continuous.smul ?_ (B.U_cont w)
    fun_prop
  have hF_per : ∀ k : ℤ, Function.Periodic (F k) a := fun k t => by
    have hUa : B.U (t + a) w = μ • B.U t w := by
      change (B.U t * B.U a) w = _
      rw [← B.U_add]
      change B.U (t + a) w = _
      rw [B.U_add]
      change B.U t (B.U a w) = _
      rw [hw, map_smul]
    have hωa : ω k * a = θ + 2 * Real.pi * (k : ℝ) := div_mul_cancel₀ _ ha.ne'
    have hexp_shift : Complex.exp (-Complex.I * (ω k : ℂ) * ((t + a : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * (ω k : ℂ) * (t : ℂ)) * μ⁻¹ := by
      have hsplit : -Complex.I * (ω k : ℂ) * ((t + a : ℝ) : ℂ) =
          (-Complex.I * (ω k : ℂ) * (t : ℂ)) +
            (-((θ : ℂ) * Complex.I) + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
        have hc : (ω k : ℂ) * (a : ℂ) = (θ : ℂ) + 2 * (Real.pi : ℂ) * (k : ℂ) := by
          exact_mod_cast hωa
        push_cast
        linear_combination -Complex.I * hc
      rw [hsplit, Complex.exp_add, Complex.exp_add,
        Complex.exp_int_mul_two_pi_mul_I (-k), mul_one, Complex.exp_neg, hμ_exp]
    have hμ0 : μ ≠ 0 := by intro h0; simp [h0] at hnorm
    change Complex.exp (-Complex.I * (ω k : ℂ) * ((t + a : ℝ) : ℂ)) • B.U (t + a) w = F k t
    rw [hexp_shift, hUa, smul_smul, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]
  have hw_k_zero : ∀ k : ℤ, (∫ t in (0 : ℝ)..a, F k t) = 0 := fun k => by
    refine B.eigenmode_eq_zero (hω_ne k) fun x => ?_
    have hint : IntervalIntegrable (F k) volume 0 a := (hF_cont k).intervalIntegrable 0 a
    rw [← (B.U x).intervalIntegral_comp_comm hint]
    have hstep : ∀ t : ℝ,
        B.U x (F k t) = Complex.exp (Complex.I * (ω k : ℂ) * (x : ℂ)) • F k (t + x) := fun t => by
      change B.U x (Complex.exp (-Complex.I * (ω k : ℂ) * (t : ℂ)) • B.U t w) = _
      have hUt : B.U x (B.U t w) = B.U (t + x) w := by
        rw [add_comm t x, B.U_add]; rfl
      rw [map_smul, hUt, smul_smul]
      congr 1
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hstep]
    rw [intervalIntegral.integral_smul]
    congr 1
    rw [intervalIntegral.integral_comp_add_right (fun u => F k u) x]
    have hper := (hF_per k).intervalIntegral_add_eq x 0
    simpa [zero_add] using hper
  let α : ℤ → ℝ := fun k => 2 * Real.pi * (k : ℝ) / a
  let g₁ : ℝ → H := fun t => F 0 (t - a / 2)
  have hg₁_cont : Continuous g₁ := (hF_cont 0).comp (continuous_id.sub continuous_const)
  have hg₁_fourier : ∀ k : ℤ,
      (∫ t in (0 : ℝ)..a, Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) • g₁ t) = 0 := fun k => by
    have hrel : ∀ t : ℝ,
        Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) • g₁ t =
          Complex.exp (-Complex.I * (α k : ℂ) * ((a / 2 : ℝ) : ℂ)) • F k (t - a / 2) := fun t => by
      simp only [g₁, F, smul_smul, ← Complex.exp_add]
      congr 2
      have hωk : ω k = ω 0 + α k := by simp only [ω, α]; push_cast; ring
      rw [hωk]
      push_cast
      ring
    simp_rw [hrel]
    rw [intervalIntegral.integral_smul,
      intervalIntegral.integral_comp_sub_right (fun u => F k u) (a / 2)]
    have h1 : (0 : ℝ) - a / 2 = -(a / 2) := by ring
    have h2 : a - a / 2 = -(a / 2) + a := by ring
    rw [h1, h2]
    have hper := (hF_per k).intervalIntegral_add_eq (-(a / 2)) 0
    rw [zero_add] at hper
    rw [hper, hw_k_zero k, smul_zero]
  let f : ℝ → ℂ := fun t => inner ℂ w (g₁ t)
  have hf_cont : Continuous f := continuous_const.inner hg₁_cont
  have hf_fourier : ∀ k : ℤ,
      (∫ t in (0 : ℝ)..a, Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * f t) = 0 := fun k => by
    have hint : IntervalIntegrable (fun t => Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) • g₁ t)
        volume 0 a := (Continuous.smul (by fun_prop) hg₁_cont).intervalIntegrable 0 a
    have hcomm := (innerRightCLM w).intervalIntegral_comp_comm hint
    rw [hg₁_fourier k, map_zero] at hcomm
    simpa only [innerRightCLM_apply, inner_smul_right] using hcomm
  let ψ : ℝ → ℝ := fun t => (f t).re
  have hψ_cont : Continuous ψ := Complex.continuous_re.comp hf_cont
  have hψ_fourier : ∀ k : ℤ,
      (∫ t in (0 : ℝ)..a, Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * (ψ t : ℂ)) = 0 := by
    intro k
    have h1 := hf_fourier k
    have hint_neg : IntervalIntegrable
        (fun t => Complex.exp (-Complex.I * (α (-k) : ℂ) * (t : ℂ)) * f t) volume 0 a :=
      (Continuous.mul (by fun_prop) hf_cont).intervalIntegrable 0 a
    have h2 := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint_neg
    rw [hf_fourier (-k), map_zero] at h2
    have h2' : (∫ t in (0 : ℝ)..a,
        Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * starRingEnd ℂ (f t)) = 0 := by
      refine ( Eq.trans ?_ h2 )
      refine intervalIntegral.integral_congr fun t _ => ?_
      change _ = starRingEnd ℂ (Complex.exp (-Complex.I * (α (-k) : ℂ) * (t : ℂ)) * f t)
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp only [α, Int.cast_neg, map_mul, map_neg, conj_I, Complex.conj_ofReal]
      push_cast
      ring
    have hint_f : IntervalIntegrable
        (fun t => Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * f t) volume 0 a :=
      (Continuous.mul (by fun_prop) hf_cont).intervalIntegrable 0 a
    have hint_cf : IntervalIntegrable
        (fun t => Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * starRingEnd ℂ (f t))
        volume 0 a :=
      (Continuous.mul (by fun_prop) (Complex.continuous_conj.comp hf_cont)).intervalIntegrable 0 a
    have hadd := intervalIntegral.integral_add hint_f hint_cf
    rw [h1, h2', add_zero] at hadd
    have hre_id : ∀ t : ℝ, (ψ t : ℂ) = (1 / 2 : ℂ) * (f t + starRingEnd ℂ (f t)) := fun t => by
      have h := Complex.re_eq_add_conj (f t)
      simp only [ψ]
      rw [h]
      ring
    have hrew : (fun t : ℝ => Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * (ψ t : ℂ)) =
        fun t : ℝ => (1 / 2 : ℂ) *
          (Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * f t +
            Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * starRingEnd ℂ (f t)) := by
      ext t; rw [hre_id t]; ring
    rw [hrew, intervalIntegral.integral_const_mul, ← hadd, mul_zero]
  let q : ℝ → ℝ := fun t => Real.sin (Real.pi * t / a) ^ 2
  have hq_cont : Continuous q := (Real.continuous_sin.comp (by fun_prop)).pow 2
  have hq_exp : ∀ t : ℝ, (q t : ℂ) =
      (1 / 2 : ℂ) - (1 / 4 : ℂ) * Complex.exp (-Complex.I * (α 1 : ℂ) * (t : ℂ)) -
        (1 / 4 : ℂ) * Complex.exp (-Complex.I * (α (-1) : ℂ) * (t : ℂ)) := fun t => by
    have hsin2 : Real.sin (Real.pi * t / a) ^ 2 =
        (1 - Real.cos (2 * Real.pi * t / a)) / 2 := by
      have hc2 := Real.cos_two_mul (Real.pi * t / a)
      have hs2 := Real.sin_sq (Real.pi * t / a)
      rw [show 2 * Real.pi * t / a = 2 * (Real.pi * t / a) by ring]
      linarith
    rw [show q t = Real.sin (Real.pi * t / a) ^ 2 from rfl, hsin2]
    push_cast
    rw [Complex.ofReal_cos, Complex.cos]
    have he1 : ((2 * (Real.pi : ℂ) * (t : ℂ) / (a : ℂ)) * Complex.I) =
        -Complex.I * (α (-1) : ℂ) * (t : ℂ) := by
      simp only [α, Int.cast_neg, Int.cast_one]; push_cast; ring
    have he2 : -((2 * (Real.pi : ℂ) * (t : ℂ) / (a : ℂ)) * Complex.I) =
        -Complex.I * (α 1 : ℂ) * (t : ℂ) := by
      simp only [α, Int.cast_one]; push_cast; ring
    rw [he1, he2]
    ring
  have hpow_fourier : ∀ (m : ℕ) (k : ℤ),
      (∫ t in (0 : ℝ)..a,
        Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) = 0 := by
    intro m
    induction m with
    | zero =>
        intro k
        simpa using hψ_fourier k
    | succ m ih =>
        intro k
        have hdecomp : ∀ t : ℝ,
            Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) *
                (((q t ^ (m + 1) : ℝ) : ℂ) * (ψ t : ℂ)) =
              (1 / 2 : ℂ) * (Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) *
                  (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) -
              (1 / 4 : ℂ) * (Complex.exp (-Complex.I * (α (k + 1) : ℂ) * (t : ℂ)) *
                  (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) -
              (1 / 4 : ℂ) * (Complex.exp (-Complex.I * (α (k - 1) : ℂ) * (t : ℂ)) *
                  (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) := fun t => by
          have hexp_add : ∀ r : ℤ,
              Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) *
                Complex.exp (-Complex.I * (α r : ℂ) * (t : ℂ)) =
                Complex.exp (-Complex.I * (α (k + r) : ℂ) * (t : ℂ)) := fun r => by
            rw [← Complex.exp_add]
            congr 1
            simp only [α, Int.cast_add]
            push_cast
            ring
          rw [pow_succ', Complex.ofReal_mul, hq_exp t]
          linear_combination
            -(1 / 4 : ℂ) * (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ)) * hexp_add 1 -
            (1 / 4 : ℂ) * (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ)) * hexp_add (-1)
        have hint_term : ∀ r : ℤ, IntervalIntegrable
            (fun t : ℝ => Complex.exp (-Complex.I * (α r : ℂ) * (t : ℂ)) *
              (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) volume 0 a := fun r =>
          (Continuous.mul (by fun_prop)
            ((Complex.continuous_ofReal.comp (hq_cont.pow m)).mul
              (Complex.continuous_ofReal.comp hψ_cont))).intervalIntegrable 0 a
        simp_rw [hdecomp]
        rw [intervalIntegral.integral_sub
            (((hint_term k).const_mul _).sub ((hint_term (k + 1)).const_mul _))
            ((hint_term (k - 1)).const_mul _),
          intervalIntegral.integral_sub ((hint_term k).const_mul _)
            ((hint_term (k + 1)).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, ih k, ih (k + 1), ih (k - 1)]
        ring
  have hreal_int_zero : ∀ m : ℕ, (∫ t in (0 : ℝ)..a, q t ^ m * ψ t) = 0 := fun m => by
    have h0 := hpow_fourier m 0
    have hα0 : α 0 = 0 := by simp [α]
    have hsimp : (fun t : ℝ => Complex.exp (-Complex.I * (α 0 : ℂ) * (t : ℂ)) *
        (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) = fun t : ℝ => ((q t ^ m * ψ t : ℝ) : ℂ) := by
      ext t
      rw [hα0]
      simp [Complex.ofReal_mul]
    rw [hsimp, intervalIntegral.integral_ofReal] at h0
    exact Complex.ofReal_eq_zero.mp h0
  by_contra hw_ne
  have hw_pos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (_root_.norm_pos_iff.mpr hw_ne)
  have hψ_mid : ψ (a / 2) = ‖w‖ ^ 2 := by
    simp only [ψ, f, g₁, F, sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul,
      B.U_zero, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K (𝕜 := ℂ),
      ← Complex.ofReal_pow, Complex.ofReal_re]
  obtain ⟨δ₁, hδ₁_pos, hδ₁_close⟩ :=
    Metric.continuousAt_iff.mp hψ_cont.continuousAt (‖w‖ ^ 2 / 2) (half_pos hw_pos)
  set δ : ℝ := min (δ₁ / 2) (a / 4)
  have hδ_pos : 0 < δ := lt_min (half_pos hδ₁_pos) (by positivity)
  have hδ_lt_δ₁ : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₁_pos)
  have hδ_le_a4 : δ ≤ a / 4 := min_le_right _ _
  have hψ_ge : ∀ t : ℝ, a / 2 - δ ≤ t → t ≤ a / 2 + δ → ‖w‖ ^ 2 / 2 ≤ ψ t := fun t ht1 ht2 => by
    have hd : dist t (a / 2) < δ₁ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) hδ_lt_δ₁
    have hc := hδ₁_close hd
    rw [Real.dist_eq, hψ_mid] at hc
    linarith [(abs_lt.mp hc).1]
  have hψ_abs : ∀ t : ℝ, -(‖w‖ ^ 2) ≤ ψ t := fun t => by
    have hnorm_g₁ : ‖g₁ t‖ = ‖w‖ := by
      simp only [g₁, F, norm_smul, B.norm_U]
      have hexp1 : ‖Complex.exp (-Complex.I * (ω 0 : ℂ) * ((t - a / 2 : ℝ) : ℂ))‖ = 1 := by
        have hr : -Complex.I * (ω 0 : ℂ) * ((t - a / 2 : ℝ) : ℂ) =
            ((-(ω 0 * (t - a / 2)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [hr, Complex.norm_exp_ofReal_mul_I]
      rw [hexp1, one_mul]
    have hle : |ψ t| ≤ ‖w‖ ^ 2 := by
      calc |ψ t| ≤ ‖f t‖ := Complex.abs_re_le_norm (f t)
        _ ≤ ‖w‖ * ‖g₁ t‖ := norm_inner_le_norm w (g₁ t)
        _ = ‖w‖ ^ 2 := by rw [hnorm_g₁, sq]
    linarith [(abs_le.mp hle).1]
  have hq_lt_one : ∀ {t : ℝ}, 0 ≤ t → t ≤ a → t ≠ a / 2 → q t < 1 := fun {t} ht0 hta htne => by
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * t / a)
    rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · simp [q]
    · rcases eq_or_lt_of_le hta with rfl | hta'
      · have hpi : Real.pi * a / a = Real.pi := mul_div_cancel_right₀ Real.pi ha.ne'
        simp [q, hpi]
      · rcases lt_or_gt_of_ne htne with hlt | hgt
        · have hmem : Real.pi * t / a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
            constructor
            · have hpos : 0 < Real.pi * t / a := by positivity
              linarith [Real.pi_pos]
            · rw [div_lt_iff₀ ha]
              have : Real.pi * t < Real.pi * (a / 2) :=
                mul_lt_mul_of_pos_left hlt Real.pi_pos
              linarith
          have hcos : 0 < Real.cos (Real.pi * t / a) := Real.cos_pos_of_mem_Ioo hmem
          show Real.sin (Real.pi * t / a) ^ 2 < 1
          nlinarith [sq_pos_of_pos hcos]
        · have hmem : Real.pi - Real.pi * t / a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
            constructor
            · have : Real.pi * t / a < Real.pi := by
                rw [div_lt_iff₀ ha]
                exact mul_lt_mul_of_pos_left hta' Real.pi_pos
              linarith [Real.pi_pos]
            · have : Real.pi / 2 < Real.pi * t / a := by
                rw [lt_div_iff₀ ha]
                have : Real.pi * (a / 2) < Real.pi * t :=
                  mul_lt_mul_of_pos_left hgt Real.pi_pos
                linarith
              linarith
          have hcos' : 0 < Real.cos (Real.pi - Real.pi * t / a) := Real.cos_pos_of_mem_Ioo hmem
          rw [Real.cos_pi_sub] at hcos'
          show Real.sin (Real.pi * t / a) ^ 2 < 1
          nlinarith [sq_pos_of_neg (neg_pos.mp hcos')]
  have hK₁_ne : (Set.Icc (0 : ℝ) (a / 2 - δ)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  have hK₂_ne : (Set.Icc (a / 2 + δ) a).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  obtain ⟨t₁_m, ht₁_m, ht₁_max⟩ :=
    isCompact_Icc.exists_isMaxOn hK₁_ne hq_cont.continuousOn
  obtain ⟨t₂_m, ht₂_m, ht₂_max⟩ :=
    isCompact_Icc.exists_isMaxOn hK₂_ne hq_cont.continuousOn
  set r₀ : ℝ := max (q t₁_m) (q t₂_m)
  have hr₀_nonneg : 0 ≤ r₀ := le_trans (sq_nonneg _) (le_max_left _ _)
  have hr₀_lt_one : r₀ < 1 := max_lt
    (hq_lt_one ht₁_m.1 (by linarith [ht₁_m.2]) (by linarith [ht₁_m.2]))
    (hq_lt_one (by linarith [ht₂_m.1]) ht₂_m.2 (by linarith [ht₂_m.1]))
  set r₁ : ℝ := (1 + r₀) / 2
  have hr₀_lt_r₁ : r₀ < r₁ := by linarith
  have hr₁_pos : 0 < r₁ := by linarith
  have hq_mid : q (a / 2) = 1 := by
    have harg : Real.pi * (a / 2) / a = Real.pi / 2 := by field_simp
    simp [q, harg]
  obtain ⟨η₁, hη₁_pos, hη₁_close⟩ :=
    Metric.continuousAt_iff.mp hq_cont.continuousAt ((1 - r₀) / 2) (by linarith)
  set η : ℝ := min (η₁ / 2) (δ / 2)
  have hη_pos : 0 < η := lt_min (half_pos hη₁_pos) (half_pos hδ_pos)
  have hη_lt_η₁ : η < η₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη₁_pos)
  have hη_le_δ : η ≤ δ := le_trans (min_le_right _ _) (half_le_self hδ_pos.le)
  have hq_ge_r₁ : ∀ t : ℝ, a / 2 - η ≤ t → t ≤ a / 2 + η → r₁ ≤ q t := fun t ht1 ht2 => by
    have hd : dist t (a / 2) < η₁ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) hη_lt_η₁
    have hc := hη₁_close hd
    rw [Real.dist_eq, hq_mid] at hc
    linarith [(abs_lt.mp hc).1]
  have hbound_pow : ∀ m : ℕ, η * (r₁ ^ m * (‖w‖ ^ 2 / 2)) ≤ a * (r₀ ^ m * ‖w‖ ^ 2) := fun m => by
    let G : ℝ → ℝ := fun t => q t ^ m * ψ t
    have hG_cont : Continuous G := (hq_cont.pow m).mul hψ_cont
    have hintG : ∀ c d : ℝ, IntervalIntegrable G volume c d := fun c d =>
      hG_cont.intervalIntegrable c d
    set p₀ : ℝ := 0
    set p₁ : ℝ := a / 2 - δ
    set p₂ : ℝ := a / 2 - η
    set p₃ : ℝ := a / 2 + η
    set p₄ : ℝ := a / 2 + δ
    set p₅ : ℝ := a
    have hsplit : (∫ t in p₀..p₅, G t) =
        (∫ t in p₀..p₁, G t) + (∫ t in p₁..p₂, G t) + (∫ t in p₂..p₃, G t) +
          (∫ t in p₃..p₄, G t) + (∫ t in p₄..p₅, G t) := by
      have s1 := (intervalIntegral.integral_add_adjacent_intervals (hintG p₀ p₁) (hintG p₁ p₅)).symm
      have s2 := (intervalIntegral.integral_add_adjacent_intervals (hintG p₁ p₂) (hintG p₂ p₅)).symm
      have s3 := (intervalIntegral.integral_add_adjacent_intervals (hintG p₂ p₃) (hintG p₃ p₅)).symm
      have s4 := (intervalIntegral.integral_add_adjacent_intervals (hintG p₃ p₄) (hintG p₄ p₅)).symm
      linarith
    have hb1 : -(p₁ - p₀) * (r₀ ^ m * ‖w‖ ^ 2) ≤ ∫ t in p₀..p₁, G t := by
      have hm := intervalIntegral.integral_mono_on (by linarith : p₀ ≤ p₁)
        (intervalIntegral_const (-(r₀ ^ m * ‖w‖ ^ 2))) (hintG p₀ p₁) fun t ht => by
        have hqt : q t ≤ r₀ := le_trans (ht₁_max ht) (le_max_left _ _)
        have hqm : q t ^ m ≤ r₀ ^ m := pow_le_pow_left₀ (sq_nonneg _) hqt m
        have hψt := hψ_abs t
        show -(r₀ ^ m * ‖w‖ ^ 2) ≤ q t ^ m * ψ t
        nlinarith [pow_nonneg (sq_nonneg (Real.sin (Real.pi * t / a))) m]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      linarith
    have hb2 : 0 ≤ ∫ t in p₁..p₂, G t := by
      refine intervalIntegral.integral_nonneg (by linarith : p₁ ≤ p₂) fun t ht => ?_
      exact mul_nonneg (pow_nonneg (sq_nonneg _) m) (le_trans (half_pos hw_pos).le
        (hψ_ge t ht.1 (by linarith [ht.2])))
    have hb3 : (p₃ - p₂) * (r₁ ^ m * (‖w‖ ^ 2 / 2)) ≤ ∫ t in p₂..p₃, G t := by
      have hm := intervalIntegral.integral_mono_on (by linarith : p₂ ≤ p₃)
        (intervalIntegral_const (r₁ ^ m * (‖w‖ ^ 2 / 2))) (hintG p₂ p₃) fun t ht => by
        have hqm : r₁ ^ m ≤ q t ^ m := pow_le_pow_left₀ hr₁_pos.le (hq_ge_r₁ t ht.1 ht.2) m
        have hψt : ‖w‖ ^ 2 / 2 ≤ ψ t := hψ_ge t (by linarith [ht.1]) (by linarith [ht.2])
        exact mul_le_mul hqm hψt (half_pos hw_pos).le (pow_nonneg (sq_nonneg _) m)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      exact hm
    have hb4 : 0 ≤ ∫ t in p₃..p₄, G t := by
      refine intervalIntegral.integral_nonneg (by linarith : p₃ ≤ p₄) fun t ht => ?_
      exact mul_nonneg (pow_nonneg (sq_nonneg _) m) (le_trans (half_pos hw_pos).le
        (hψ_ge t (by linarith [ht.1]) ht.2))
    have hb5 : -(p₅ - p₄) * (r₀ ^ m * ‖w‖ ^ 2) ≤ ∫ t in p₄..p₅, G t := by
      have hm := intervalIntegral.integral_mono_on (by linarith : p₄ ≤ p₅)
        (intervalIntegral_const (-(r₀ ^ m * ‖w‖ ^ 2))) (hintG p₄ p₅) fun t ht => by
        have hqt : q t ≤ r₀ := le_trans (ht₂_max ht) (le_max_right _ _)
        have hqm : q t ^ m ≤ r₀ ^ m := pow_le_pow_left₀ (sq_nonneg _) hqt m
        have hψt := hψ_abs t
        show -(r₀ ^ m * ‖w‖ ^ 2) ≤ q t ^ m * ψ t
        nlinarith [pow_nonneg (sq_nonneg (Real.sin (Real.pi * t / a))) m]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      linarith
    have hzero : ∫ t in p₀..p₅, G t = 0 := hreal_int_zero m
    have hlen : (p₁ - p₀) + (p₅ - p₄) ≤ a := by simp only [p₀, p₁, p₄, p₅]; linarith
    have hp32 : 2 * η = p₃ - p₂ := by simp only [p₂, p₃]; ring
    have hr0w : 0 ≤ r₀ ^ m * ‖w‖ ^ 2 := mul_nonneg (pow_nonneg hr₀_nonneg m) hw_pos.le
    have hr1w : 0 ≤ r₁ ^ m * (‖w‖ ^ 2 / 2) := mul_nonneg (pow_nonneg hr₁_pos.le m) (half_pos hw_pos).le
    nlinarith
  have hratio_le : ∀ m : ℕ, η / (2 * a) ≤ (r₀ / r₁) ^ m := fun m => by
    have hm := hbound_pow m
    rw [div_pow, le_div_iff₀ (pow_pos hr₁_pos m), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hratio_lt_one : r₀ / r₁ < 1 := (div_lt_one hr₁_pos).mpr hr₀_lt_r₁
  have htend0 : Tendsto (fun m : ℕ => (r₀ / r₁) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr₀_nonneg hr₁_pos.le) hratio_lt_one
  have hle0 : η / (2 * a) ≤ 0 := ge_of_tendsto' htend0 hratio_le
  linarith [div_pos hη_pos (by positivity : (0 : ℝ) < 2 * a)]

/-- **No non-identity eigenvectors at nonzero shift.** In any `BorchersPair`, if `a ≠ 0`, `μ ≠ 1`,
and `U(a) w = μ • w`, then `w = 0`. -/
theorem eigenvector_eq_zero_of_ne_one [CompleteSpace H] (B : BorchersPair H)
    {a : ℝ} (ha : a ≠ 0) {μ : ℂ} (hμ : μ ≠ 1) {w : H} (hw : B.U a w = μ • w) :
    w = 0 := by
  by_cases hnorm : ‖μ‖ = 1
  · rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · have hμ0 : μ ≠ 0 := by intro h0; simp [h0] at hnorm
      have hw_neg : B.U (-a) w = μ⁻¹ • w := by
        calc B.U (-a) w = B.U (-a) (μ⁻¹ • (μ • w)) := by
              rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
          _ = μ⁻¹ • B.U (-a) (B.U a w) := by rw [hw, map_smul]
          _ = μ⁻¹ • ((B.U (-a) * B.U a) w) := rfl
          _ = μ⁻¹ • w := by rw [B.U_neg_mul]; rfl
      refine B.eigenvector_eq_zero_of_pos (neg_pos.mpr ha_neg) (by simp [hnorm]) ?_ hw_neg
      exact inv_ne_one.mpr hμ
    · exact B.eigenvector_eq_zero_of_pos ha_pos hnorm hμ hw
  · have h1 : ‖w‖ = ‖μ‖ * ‖w‖ := by
      calc ‖w‖ = ‖B.U a w‖ := (B.norm_U a w).symm
        _ = ‖μ • w‖ := by rw [hw]
        _ = ‖μ‖ * ‖w‖ := norm_smul μ w
    have h2 : (1 - ‖μ‖) * ‖w‖ = 0 := by linarith
    exact norm_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hnorm)))

/-- **Triviality on finite-dimensional invariant subspaces.** Every finite-dimensional `ℂ`-subspace
`V ≤ H` invariant under `B.U` is fixed pointwise by `B.U`. -/
theorem trivial_on_finiteDimensional [CompleteSpace H] (B : BorchersPair H)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hinv : ∀ (a : ℝ), ∀ v ∈ V, B.U a v ∈ V) (a : ℝ) {v : H} (hv : v ∈ V) :
    B.U a v = v := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [B.U_zero]
  let V_op : V ≃ₗᵢ[ℂ] V :=
    { toFun := fun x => ⟨B.U a x.1, hinv a x.1 x.2⟩
      invFun := fun x => ⟨B.U (-a) x.1, hinv (-a) x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by change (B.U (-a) * B.U a) x.1 = x.1; rw [B.U_neg_mul]; rfl)
      right_inv := fun x => Subtype.ext (by change (B.U a * B.U (-a)) x.1 = x.1; rw [B.U_mul_neg]; rfl)
      map_add' := fun x y => Subtype.ext (map_add (B.U a) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul (B.U a) c x.1)
      norm_map' := fun x => B.norm_U a x.1 }
  let K : Submodule ℂ V := LinearMap.ker (V_op.toLinearEquiv.toLinearMap - LinearMap.id)
  have hK_mem : ∀ x : V, x ∈ K ↔ V_op x = x := fun x => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hK_perp_inv : ∀ y ∈ Kᗮ, V_op y ∈ Kᗮ ∧ V_op.symm y ∈ Kᗮ := fun y hy => by
    rw [Submodule.mem_orthogonal] at hy
    refine ⟨Submodule.mem_orthogonal.mpr fun x hx => ?_,
      Submodule.mem_orthogonal.mpr fun x hx => ?_⟩
    · have hx' : V_op.symm x = x := V_op.injective (by rw [V_op.apply_symm_apply, (hK_mem x).mp hx])
      calc inner ℂ x (V_op y) = inner ℂ (V_op (V_op.symm x)) (V_op y) := by
            rw [V_op.apply_symm_apply]
        _ = inner ℂ (V_op.symm x) y := V_op.inner_map_map _ _
        _ = inner ℂ x y := by rw [hx']
        _ = 0 := hy x hx
    · have hx' : V_op x = x := (hK_mem x).mp hx
      calc inner ℂ x (V_op.symm y) = inner ℂ (V_op.symm (V_op x)) (V_op.symm y) := by
            rw [V_op.symm_apply_apply]
        _ = inner ℂ (V_op x) y := V_op.symm.inner_map_map _ _
        _ = inner ℂ x y := by rw [hx']
        _ = 0 := hy x hx
  have hK_perp_bot : Kᗮ = ⊥ := by
    by_contra hne
    obtain ⟨y₀, hy₀_mem, hy₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    haveI : Nontrivial Kᗮ := ⟨⟨0, ⟨y₀, hy₀_mem⟩, Ne.symm (Subtype.coe_ne_coe.mp hy₀_ne)⟩⟩
    let W_op : Kᗮ ≃ₗᵢ[ℂ] Kᗮ :=
      { toFun := fun y => ⟨V_op y.1, (hK_perp_inv y.1 y.2).1⟩
        invFun := fun y => ⟨V_op.symm y.1, (hK_perp_inv y.1 y.2).2⟩
        left_inv := fun y => Subtype.ext (V_op.symm_apply_apply y.1)
        right_inv := fun y => Subtype.ext (V_op.apply_symm_apply y.1)
        map_add' := fun x y => Subtype.ext (map_add V_op x.1 y.1)
        map_smul' := fun c y => Subtype.ext (map_smul V_op c y.1)
        norm_map' := fun y => V_op.norm_map y.1 }
    obtain ⟨u, μ, hu_ne, hu_eig, _⟩ := HTGeometry.exists_unimodular_eigenvector W_op
    have huH_ne : ((u : V) : H) ≠ 0 := by
      intro h0
      exact hu_ne (Subtype.ext (Subtype.ext h0))
    by_cases hμ : μ = 1
    · subst hμ
      have huK : (u : V) ∈ K := by
        rw [hK_mem]
        have he := congr_arg Subtype.val hu_eig
        simpa using he
      have hu0 : (u : V) = 0 := by
        have hinner : inner ℂ (u : V) (u : V) = 0 := (Submodule.mem_orthogonal.mp u.2) (u : V) huK
        exact inner_self_eq_zero.mp hinner
      exact hu_ne (Subtype.ext hu0)
    · have huH_eig : B.U a ((u : V) : H) = μ • ((u : V) : H) :=
        congr_arg Subtype.val (congr_arg Subtype.val hu_eig)
      exact huH_ne (B.eigenvector_eq_zero_of_ne_one ha hμ huH_eig)
  have hK_top : K = ⊤ := by
    haveI : CompleteSpace K := FiniteDimensional.complete ℂ K
    rw [← K.orthogonal_orthogonal, hK_perp_bot, Submodule.bot_orthogonal_eq_top]
  have hvK : (⟨v, hv⟩ : V) ∈ K := hK_top ▸ Submodule.mem_top
  exact congr_arg Subtype.val ((hK_mem ⟨v, hv⟩).mp hvK)

/-- **Graph black hole no-go.** For every graph black hole algebra `QuadraticAlgebra ℝ (-q) t`
(damped or undamped), if the cyclic subspace generated by a representation `π` on a vector `Ω` is
invariant under `B.U`, then `B.U` fixes every state `π(z) Ω` identically. -/
theorem no_nontrivial_borchers_on_quadraticAlgebra [CompleteSpace H] (B : BorchersPair H)
    {q t : ℝ} (π : QuadraticAlgebra ℝ (-q) t →ₐ[ℝ] H →L[ℂ] H) (Ω : H)
    (hinv : ∀ (a : ℝ) (z : QuadraticAlgebra ℝ (-q) t),
      B.U a (π z Ω) ∈ Submodule.span ℂ ({Ω, π QuadraticAlgebra.ω Ω} : Set H))
    (a : ℝ) (z : QuadraticAlgebra ℝ (-q) t) :
    B.U a (π z Ω) = π z Ω := by
  set V : Submodule ℂ H := Submodule.span ℂ ({Ω, π QuadraticAlgebra.ω Ω} : Set H)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hr_smul : ∀ (r : ℝ) (v : H), r • v = (r : ℂ) • v := fun r v => by
    rw [← one_smul ℂ v, ← smul_assoc, Complex.real_smul, mul_one]
  have hz_mem : ∀ w : QuadraticAlgebra ℝ (-q) t, π w Ω ∈ V := fun w => by
    have hw_eq : w = algebraMap ℝ _ w.re + w.im • QuadraticAlgebra.ω := by
      ext <;> simp [QuadraticAlgebra.ω]
    have hπw : π w Ω = (w.re : ℂ) • Ω + (w.im : ℂ) • (π QuadraticAlgebra.ω Ω) := by
      rw [hw_eq, map_add, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul]
      change (w.re • (1 : H →L[ℂ] H)) Ω + (w.im • π QuadraticAlgebra.ω) Ω = _
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, hr_smul]
    rw [hπw]
    exact add_mem (V.smul_mem _ (Submodule.subset_span (by simp)))
      (V.smul_mem _ (Submodule.subset_span (by simp)))
  have hV_inv : ∀ (b : ℝ), ∀ v ∈ V, B.U b v ∈ V := fun b v hv => by
    refine Submodule.span_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => by rw [map_add]; exact add_mem hx hy)
      (fun c x _ hx => by rw [map_smul]; exact V.smul_mem c hx) hv
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · simpa [map_one] using hinv b 1
    · rw [Set.mem_singleton_iff.mp hx']
      exact hinv b QuadraticAlgebra.ω
  exact B.trivial_on_finiteDimensional V hV_inv a (hz_mem z)

/-- **Triviality of antiperiodic vectors.** In any `BorchersPair`, `U(τ) w = -w` (`τ ≠ 0`) forces
`w = 0`. -/
theorem antiperiodic_eq_zero [CompleteSpace H] (B : BorchersPair H)
    {τ : ℝ} (hτ : τ ≠ 0) {w : H} (hw : B.U τ w = -w) : w = 0 :=
  B.eigenvector_eq_zero_of_ne_one hτ (by norm_num : (-1 : ℂ) ≠ 1) (by simpa using hw)

/-- **Vanishing of alternating Cesàro Bohr averages.** For every nonzero frequency `γ ≠ 0` and
every vector `ψ ∈ H`, `(1 / K) ∑_{k < K} (-1)^k ⟪ψ, U(k π / γ) ψ⟫ → 0` as `K → ∞`. -/
theorem alternating_cesaro_tendsto_zero [CompleteSpace H] (B : BorchersPair H)
    {γ : ℝ} (hγ : γ ≠ 0) (ψ : H) :
    Tendsto (fun K : ℕ =>
      (∑ k ∈ Finset.range K, (-1 : ℂ) ^ k * inner ℂ ψ (B.U ((k : ℝ) * Real.pi / γ) ψ)) / (K : ℂ))
      atTop (𝓝 0) := by
  set τ : ℝ := Real.pi / γ
  have hτ : τ ≠ 0 := div_ne_zero Real.pi_ne_zero hγ
  set W : H →L[ℂ] H := -B.U τ
  have hW_pow : ∀ (k : ℕ) (v : H), (W ^ k) v = (-1 : ℂ) ^ k • B.U ((k : ℝ) * τ) v := by
    intro k
    induction k with
    | zero => intro v; simp [B.U_zero]
    | succ k ih =>
        intro v
        change (W * W ^ k) v = _
        change W ((W ^ k) v) = _
        rw [ih v, map_smul]
        have hstep : W (B.U ((k : ℝ) * τ) v) = (-1 : ℂ) • B.U (((k + 1 : ℕ) : ℝ) * τ) v := by
          simp only [W, ContinuousLinearMap.neg_apply, neg_one_smul]
          congr 1
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm ((k : ℝ) * τ) τ, B.U_add]
          rfl
        rw [hstep, smul_smul, pow_succ]
  have hW_norm : ∀ (k : ℕ) (v : H), ‖(W ^ k) v‖ = ‖v‖ := fun k v => by
    rw [hW_pow k v, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, B.norm_U]
  let R : Submodule ℂ H := LinearMap.range ((W - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)
  have hR_perp : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [Submodule.mem_orthogonal] at hz
    have hadj0 : (star (W - 1 : H →L[ℂ] H)) z = 0 := by
      have hself : inner ℂ ((W - 1 : H →L[ℂ] H) ((star (W - 1 : H →L[ℂ] H)) z)) z = 0 :=
        hz _ ⟨(star (W - 1 : H →L[ℂ] H)) z, rfl⟩
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at hself
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact inner_self_eq_zero.mp hself
    have hanti : B.U (-τ) z = -z := by
      rw [star_sub, star_one, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        sub_eq_zero] at hadj0
      have hstarW : star W = -B.U (-τ) := by simp only [W, star_neg, B.star_U]
      rw [hstarW, ContinuousLinearMap.neg_apply, neg_eq_iff_eq_neg] at hadj0
      exact hadj0
    exact B.antiperiodic_eq_zero (neg_ne_zero.mpr hτ) hanti
  have hR_dense : ∀ δ > 0, ∃ x : H, ‖ψ - (W - 1) x‖ < δ := by
    intro δ hδ
    have hcl_top : R.topologicalClosure = ⊤ := by
      have hp : R.topologicalClosureᗮ = ⊥ := by
        rwa [Submodule.topologicalClosure_orthogonal]
      rw [← R.topologicalClosure.orthogonal_orthogonal, hp, Submodule.bot_orthogonal_eq_top]
    have hmem : ψ ∈ closure (R : Set H) := by
      change ψ ∈ R.topologicalClosure
      rw [hcl_top]
      exact Submodule.mem_top
    obtain ⟨y, ⟨x, rfl⟩, hxy⟩ := Metric.mem_closure_iff.mp hmem δ hδ
    exact ⟨x, by simpa [dist_eq_norm] using hxy⟩
  have htele : ∀ (K : ℕ) (x : H),
      ∑ k ∈ Finset.range K, (W ^ k) ((W - 1) x) = (W ^ K) x - x := by
    intro K x
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, ih]
        have hstep : (W ^ K) ((W - 1) x) = (W ^ (K + 1)) x - (W ^ K) x := by
          rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.one_apply, pow_succ']
          rfl
        rw [hstep]
        abel
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := ‖ψ‖ + 1
  have hM_pos : 0 < M := by positivity
  obtain ⟨x, hx⟩ := hR_dense (ε / (2 * M)) (div_pos hε (by positivity))
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (4 * M * ‖x‖ / ε + 1)
  refine ⟨K₀, fun K hK => ?_⟩
  have hK_gt1 : (1 : ℝ) < (K : ℝ) := by
    have hpos : 0 ≤ 4 * M * ‖x‖ / ε := by positivity
    have hk0 : 4 * M * ‖x‖ / ε + 1 < (K : ℝ) := lt_of_lt_of_le hK₀ (by exact_mod_cast hK)
    linarith
  have hK_pos : (0 : ℝ) < (K : ℝ) := by linarith
  have hterm_eq : ∀ k : ℕ,
      (-1 : ℂ) ^ k * inner ℂ ψ (B.U ((k : ℝ) * Real.pi / γ) ψ) = inner ℂ ψ ((W ^ k) ψ) := fun k => by
    have harg : (k : ℝ) * Real.pi / γ = (k : ℝ) * τ := by simp only [τ]; ring
    rw [hW_pow k ψ, inner_smul_right, harg]
  simp_rw [hterm_eq, ← inner_sum]
  rw [dist_zero_right, norm_div, Complex.norm_natCast]
  have hsplit_sum : ∑ k ∈ Finset.range K, (W ^ k) ψ =
      (∑ k ∈ Finset.range K, (W ^ k) (ψ - (W - 1) x)) + ((W ^ K) x - x) := by
    rw [← htele K x, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_add, sub_add_cancel]
  have hsum_norm : ‖∑ k ∈ Finset.range K, (W ^ k) ψ‖ ≤
      (K : ℝ) * (ε / (2 * M)) + 2 * ‖x‖ := by
    rw [hsplit_sum]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖∑ k ∈ Finset.range K, (W ^ k) (ψ - (W - 1) x)‖
          ≤ ∑ k ∈ Finset.range K, ‖(W ^ k) (ψ - (W - 1) x)‖ := norm_sum_le _ _
        _ = ∑ _ ∈ Finset.range K, ‖ψ - (W - 1) x‖ :=
            Finset.sum_congr rfl fun k _ => hW_norm k _
        _ = (K : ℝ) * ‖ψ - (W - 1) x‖ := by simp
        _ ≤ (K : ℝ) * (ε / (2 * M)) := mul_le_mul_of_nonneg_left hx.le hK_pos.le
    · calc ‖(W ^ K) x - x‖ ≤ ‖(W ^ K) x‖ + ‖x‖ := norm_sub_le _ _
        _ = 2 * ‖x‖ := by rw [hW_norm K x]; ring
  have hcs : ‖inner ℂ ψ (∑ k ∈ Finset.range K, (W ^ k) ψ)‖ ≤
      M * ((K : ℝ) * (ε / (2 * M)) + 2 * ‖x‖) := by
    calc ‖inner ℂ ψ (∑ k ∈ Finset.range K, (W ^ k) ψ)‖
        ≤ ‖ψ‖ * ‖∑ k ∈ Finset.range K, (W ^ k) ψ‖ := norm_inner_le_norm _ _
      _ ≤ M * ((K : ℝ) * (ε / (2 * M)) + 2 * ‖x‖) :=
          mul_le_mul (by simp [M]) hsum_norm (norm_nonneg _) hM_pos.le
  rw [div_lt_iff₀ hK_pos]
  have htail : 2 * M * ‖x‖ < (K : ℝ) * (ε / 2) := by
    have hk0 : 4 * M * ‖x‖ / ε < (K : ℝ) := by
      have h1 : 4 * M * ‖x‖ / ε + 1 < (K : ℝ) := lt_of_lt_of_le hK₀ (by exact_mod_cast hK)
      linarith
    rw [div_lt_iff₀ hε] at hk0
    nlinarith [norm_nonneg x]
  have hmain : M * ((K : ℝ) * (ε / (2 * M))) = (K : ℝ) * (ε / 2) := by
    field_simp
  nlinarith

end BorchersPair

end GaloisForLFunctions.CountingHolography

