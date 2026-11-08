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
open GaloisForLFunctions.SquareRootThreshold (zetaZeroConfig temperedConfig_zetaZeroConfig)

/-! ### 1. Antiunitary generator–correlation dichotomy and cross-horizon Hankel law -/

/-- Any antiunitary involution on a complex Hilbert space is a continuous `ℝ`-linear isometry. -/
def AntiunitaryInvol.toRealCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (J : AntiunitaryInvol H) : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := J
      map_add' := J.map_add
      map_smul' := fun (r : ℝ) (x : H) => by
        have hr : ∀ y : H, r • y = (r : ℂ) • y := fun y => by
          calc r • y = r • ((1 : ℂ) • y) := by rw [one_smul]
            _ = (r • (1 : ℂ)) • y := (smul_assoc r (1 : ℂ) y).symm
            _ = ((r : ℂ) * 1) • y := by rw [Complex.real_smul]
            _ = (r : ℂ) • y := by rw [mul_one]
        show J (r • x) = r • J x
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
          (ContinuousLinearMap.adjoint_inner_right P x y).symm
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
def covShift {S H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : S → H →L[ℂ] H) (s : S) (A₀ : H →L[ℂ] H) : H →L[ℂ] H :=
  U s * A₀ * star (U s)

@[simp] theorem covShift_apply {S H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : S → H →L[ℂ] H) (s : S) (A₀ : H →L[ℂ] H) (x : H) :
    covShift U s A₀ x = U s (A₀ ((star (U s)) x)) := rfl

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
    calc ms.J.conjOp (covShift U t B₀) ms.Ω
        = ms.J (U t (B₀ ((star (U t)) ms.Ω))) := by
            rw [AntiunitaryInvol.conjOp_apply, covShift_apply, ms.J_omega]
      _ = ms.J (U t (ms.J (ms.J (B₀ ms.Ω)))) := by rw [hstarΩ t, ms.J.invol]
      _ = (ms.J.conjOp (U t)) (ms.J (B₀ ms.Ω)) := rfl
      _ = (star (U t)) (ms.J (B₀ ms.Ω)) := by rw [hJ t]
  rw [hright, covShift_apply]
  have hadj1 : ∀ v : H, inner ℂ ms.Ω (U s v) = inner ℂ ms.Ω v := fun v => by
    calc inner ℂ ms.Ω (U s v) = inner ℂ (ContinuousLinearMap.adjoint (U s) ms.Ω) v :=
          (ContinuousLinearMap.adjoint_inner_left (U s) v ms.Ω).symm
      _ = inner ℂ ((star (U s)) ms.Ω) v := by rw [← ContinuousLinearMap.star_eq_adjoint]
      _ = inner ℂ ms.Ω v := by rw [hstarΩ s]
  have hadj2 : ∀ v : H, inner ℂ ms.Ω (A₀ v) = inner ℂ ((star A₀) ms.Ω) v := fun v => by
    calc inner ℂ ms.Ω (A₀ v) = inner ℂ (ContinuousLinearMap.adjoint A₀ ms.Ω) v :=
          (ContinuousLinearMap.adjoint_inner_left A₀ v ms.Ω).symm
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
    exact congr_arg h (Subtype.ext (sqFreeCore_sq_mul p k))

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
      calc ((a : ℕ) : ℝ) = ((q.num.natAbs : ℤ) : ℝ) := by norm_cast
        _ = (q.num : ℝ) := by rw [Int.natAbs_of_nonneg hnum_pos.le]
    have hb : (b : ℝ) = (q.den : ℝ) := rfl
    rw [ha, hb]
    exact_mod_cast Rat.num_div_den q
  refine ⟨c * Real.log ((a : ℝ) / (b : ℝ)), ?_, ⟨a, b, rfl⟩⟩
  rw [Metric.mem_ball, hdiv, ← hval]
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
    calc (a ^ 2 : ℕ+) * b ^ 2 = (a * a) * (b * b) := by rw [sq, sq]
      _ = (a * b) * (a * b) := mul_mul_mul_comm a a b b
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
    rw [ae_iff, show {lam : ℝ | ¬ 0 ≤ lam} = Set.Iio 0 by ext lam; simp]
    exact hsupp
  have hint_exp : ∀ n : ℕ+, Integrable (fun lam : ℝ => Real.exp (-lam * Real.log (n : ℝ))) μ := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt n.pos
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

private theorem h2_memℓp (f : Fin 2 × Fin 2 → ℂ) : Memℓp f 2 :=
  memℓp_gen (hasSum_fintype _).summable

private theorem h2_norm_sq (X : H2) : ‖X‖ ^ 2 = ∑ p : Fin 2 × Fin 2, ‖X p‖ ^ 2 := by
  have h1 : (inner ℂ X X).re = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
  rw [← h1, lp.inner_eq_tsum, tsum_fintype, Complex.re_sum]
  exact Finset.sum_congr rfl fun p _ => inner_self_eq_norm_sq (𝕜 := ℂ) (X p)

private theorem h2_entry_le_norm (X : H2) (q : Fin 2 × Fin 2) : ‖X q‖ ≤ ‖X‖ := by
  have hle : ‖X q‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [h2_norm_sq]
    exact Finset.single_le_sum (f := fun p : Fin 2 × Fin 2 => ‖X p‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ q)
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
        h2_memℓp _⟩
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
        h2_memℓp _⟩
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
        h2_memℓp _⟩
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
        h2_memℓp _⟩
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
    h2_memℓp _⟩
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
    h2_memℓp _⟩

@[simp] private theorem Ω2_apply (p : Fin 2 × Fin 2) :
    Ω2 p = if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := rfl

private theorem leftMul2_Ω2 (A : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 2 × Fin 2) :
    leftMul2 A Ω2 p = ((1 / Real.sqrt 2 : ℝ) : ℂ) * A p.1 p.2 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

private theorem rightMul2_Ω2 (B : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 2 × Fin 2) :
    rightMul2 B Ω2 p = ((1 / Real.sqrt 2 : ℝ) : ℂ) * B p.1 p.2 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp

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
  rw [lp.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, rightMul2_Ω2, ← mul_assoc,
    sqrt2_mul_inv_sqrt2, one_mul]
  simp [E2, Pi.single_apply]

private theorem single_eq_leftMul2_Ω2 (i j : Fin 2) :
    lp.single (E := fun _ : Fin 2 × Fin 2 => ℂ) 2 (i, j) 1 =
      ((Real.sqrt 2 : ℝ) : ℂ) • leftMul2 (E2 i j) Ω2 := by
  ext ⟨r, s⟩
  rw [lp.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, leftMul2_Ω2, ← mul_assoc,
    sqrt2_mul_inv_sqrt2, one_mul]
  simp [E2, Pi.single_apply]

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
  simp only [_root_.sub_apply, lp.coeFn_sub, Pi.sub_apply, leftMul2_Ω2, A,
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
        congr_arg (fun U : H2 →L[ℂ] H2 => U Ω2) hcomm.symm
      rw [h0, map_zero] at happ
      rw [single_eq_leftMul2_Ω2 i j, map_smul, happ, smul_zero]
    ext X
    rw [h2_eq_sum_single X, map_sum]
    simp [hsingle]
  let B : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => ((Real.sqrt 2 : ℝ) : ℂ) * T Ω2 (i, j)
  refine ⟨B, sub_eq_zero.mp (hsep _ (sub_mem hT (rightMul2_mem_commutant B)) ?_)⟩
  ext ⟨i, j⟩
  simp only [_root_.sub_apply, lp.coeFn_sub, Pi.sub_apply, rightMul2_Ω2, B,
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
            (ContinuousLinearMap.adjoint_inner_left (leftMul2 A) (leftMul2 Aᴴ Ω2) Ω2).symm
        _ = inner ℂ ((star (leftMul2 A)) Ω2) (leftMul2 Aᴴ Ω2) := by
            rw [← ContinuousLinearMap.star_eq_adjoint]
        _ = inner ℂ (leftMul2 Aᴴ Ω2) (leftMul2 Aᴴ Ω2) := by rw [star_leftMul2]
    have hsq : (inner ℂ (leftMul2 Aᴴ Ω2) (leftMul2 Aᴴ Ω2)).re = ‖leftMul2 Aᴴ Ω2‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [hadj, hsq]
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
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D2, Matrix.mul_apply, Fin.sum_univ_two, chi2_sq]

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
      rw [← Complex.ofReal_mul, one_div_mul_one_div, Real.mul_self_sqrt zero_le_two]
      push_cast; rfl
    rw [hadj, lp.inner_eq_tsum, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [leftMul2_Ω2, Matrix.conjTranspose_apply, Bm, Bn, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply,
      RCLike.star_def, chi2_conj, map_mul, map_one, map_zero, Complex.conj_ofReal,
      mul_zero, add_zero]
    have hcomb : (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1) * (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1) +
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * chi2 n) * (((1 / Real.sqrt 2 : ℝ) : ℂ) * chi2 m) =
        (1 / 2 : ℂ) * (1 + chi2 (m * n)) := by
      rw [chi2_mul]
      linear_combination (1 + chi2 m * chi2 n) * hsq2
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcomb, hhalf, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
    ring
  have hsq_class : ∀ p k : ℕ+,
      (1 + (chi2 (p ^ 2 * k)).re) / 2 = (1 + (chi2 k).re) / 2 := fun p k => by
    rw [sq, mul_assoc, chi2_mul, chi2_mul, ← mul_assoc, chi2_sq, one_mul]
  obtain ⟨hHankel, hHecke⟩ := (isMulHankel_and_heckeInv_iff_sqClass K).mpr
    ⟨fun k => (1 + (chi2 k).re) / 2, hsq_class, hK_val⟩
  refine ⟨hHankel, hHecke, ?_, ?_⟩
  · rw [hK_val, one_mul, chi2_one]; norm_num
  · rw [hK_val, one_mul, chi2_two]; norm_num

end Mat2Realization

/-! ### 3. Borchers `ax + b` spectral and Bohr-frequency rigidity -/

/-- A strongly continuous unitary Borchers pair `(Δ, U)` on a complex Hilbert space satisfying the
half-sided modular scaling relation `Δ(s) U(a) Δ(-s) = U(e^{-2πs} a)`. -/
structure BorchersPair (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem U_mul_neg (B : BorchersPair H) (a : ℝ) : B.U a * B.U (-a) = 1 := by
  rw [← B.U_add, add_neg_cancel, B.U_zero]

theorem U_neg_mul (B : BorchersPair H) (a : ℝ) : B.U (-a) * B.U a = 1 := by
  rw [← B.U_add, neg_add_cancel, B.U_zero]

theorem star_U (B : BorchersPair H) (a : ℝ) : star (B.U a) = B.U (-a) := by
  calc star (B.U a) = star (B.U a) * (B.U a * B.U (-a)) := by rw [B.U_mul_neg, mul_one]
    _ = (star (B.U a) * B.U a) * B.U (-a) := (mul_assoc _ _ _).symm
    _ = B.U (-a) := by rw [B.U_iso, one_mul]

theorem U_mul_star (B : BorchersPair H) (a : ℝ) :
    B.U a * star (B.U a) = 1 := by
  rw [B.star_U, B.U_mul_neg]

theorem Δ_mul_neg (B : BorchersPair H) (s : ℝ) : B.Δ s * B.Δ (-s) = 1 := by
  rw [← B.Δ_add, add_neg_cancel, B.Δ_zero]

theorem Δ_neg_mul (B : BorchersPair H) (s : ℝ) : B.Δ (-s) * B.Δ s = 1 := by
  rw [← B.Δ_add, neg_add_cancel, B.Δ_zero]

theorem inner_U (B : BorchersPair H) (a : ℝ) (x y : H) :
    inner ℂ (B.U a x) (B.U a y) = inner ℂ x y := by
  calc inner ℂ (B.U a x) (B.U a y)
      = inner ℂ x (ContinuousLinearMap.adjoint (B.U a) (B.U a y)) :=
        (ContinuousLinearMap.adjoint_inner_right (B.U a) x (B.U a y)).symm
    _ = inner ℂ x ((star (B.U a) * B.U a) y) := by
        rw [← ContinuousLinearMap.star_eq_adjoint]; rfl
    _ = inner ℂ x y := by rw [B.U_iso]; rfl

theorem norm_U (B : BorchersPair H) (a : ℝ) (x : H) :
    ‖B.U a x‖ = ‖x‖ := by
  have hsq : ‖B.U a x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), B.inner_U]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

theorem norm_Δ (B : BorchersPair H) (s : ℝ) (x : H) :
    ‖B.Δ s x‖ = ‖x‖ := by
  have hinner : inner ℂ (B.Δ s x) (B.Δ s x) = inner ℂ x x := by
    calc inner ℂ (B.Δ s x) (B.Δ s x)
        = inner ℂ x (ContinuousLinearMap.adjoint (B.Δ s) (B.Δ s x)) :=
          (ContinuousLinearMap.adjoint_inner_right (B.Δ s) x (B.Δ s x)).symm
      _ = inner ℂ x ((star (B.Δ s) * B.Δ s) x) := by
          rw [← ContinuousLinearMap.star_eq_adjoint]; rfl
      _ = inner ℂ x x := by rw [B.Δ_iso]; rfl
  have hsq : ‖B.Δ s x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- **Forced vacuum invariance.** Any vector fixed by the modular flow `Δ` is automatically fixed
by the entire translation group `U`. -/
theorem fix_of_delta_fix (B : BorchersPair H) {Ω : H}
    (hΔ : ∀ s : ℝ, B.Δ s Ω = Ω) (a : ℝ) : B.U a Ω = Ω := by
  have hnorm_eq : ∀ s : ℝ, ‖B.U a Ω - Ω‖ = ‖B.U (Real.exp (-2 * Real.pi * s) * a) Ω - Ω‖ := by
    intro s
    calc ‖B.U a Ω - Ω‖ = ‖B.Δ s (B.U a Ω - Ω)‖ := (B.norm_Δ s _).symm
      _ = ‖B.Δ s (B.U a (B.Δ (-s) Ω)) - Ω‖ := by rw [map_sub, hΔ (-s), hΔ s]
      _ = ‖(B.Δ s * B.U a * B.Δ (-s)) Ω - Ω‖ := rfl
      _ = ‖B.U (Real.exp (-2 * Real.pi * s) * a) Ω - Ω‖ := by rw [B.borchers]
  have htend_arg : Tendsto (fun s : ℝ => Real.exp (-2 * Real.pi * s) * a) atTop (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => -(2 * Real.pi * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))
    have hexp0 : Tendsto (fun s : ℝ => Real.exp (-2 * Real.pi * s)) atTop (𝓝 0) := by
      have heq : (fun s : ℝ => Real.exp (-2 * Real.pi * s)) =
          Real.exp ∘ fun s : ℝ => -(2 * Real.pi * s) := by ext s; simp [neg_mul]
      rw [heq]
      exact Real.tendsto_exp_atBot.comp hlin
    simpa only [zero_mul] using hexp0.mul_const a
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
theorem mem_iff_eq_one (B : BorchersPair H) {M : VonNeumannAlgebra H}
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
theorem eigenmode_eq_zero (B : BorchersPair H) {ω : ℝ} (hω : ω ≠ 0) {v : H}
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

omit [CompleteSpace H] in
@[simp] private theorem innerRightCLM_apply (w y : H) : innerRightCLM w y = inner ℂ w y := rfl

private theorem peaked_integral_pow_zero_imp_le_zero {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    {ψ : ℝ → ℝ} (hψ_cont : Continuous ψ) (hψ_mid : ψ (a / 2) = M)
    (hψ_abs : ∀ t : ℝ, -M ≤ ψ t)
    (hint_zero : ∀ m : ℕ,
      (∫ t in (0 : ℝ)..a, (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) = 0) :
    M ≤ 0 := by
  by_contra hM_not
  have hM_pos : 0 < M := lt_of_not_ge hM_not
  have hq_cont : Continuous (fun t : ℝ => Real.sin (Real.pi * t / a) ^ 2) :=
    (Real.continuous_sin.comp (by fun_prop)).pow 2
  obtain ⟨δ₁, hδ₁_pos, hδ₁_close⟩ :=
    Metric.continuousAt_iff.mp hψ_cont.continuousAt (M / 2) (half_pos hM_pos)
  set δ : ℝ := min (δ₁ / 2) (a / 4)
  have hδ_pos : 0 < δ := lt_min (half_pos hδ₁_pos) (by positivity)
  have hδ_lt_δ₁ : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₁_pos)
  have hδ_le_a4 : δ ≤ a / 4 := min_le_right _ _
  have hψ_ge : ∀ t : ℝ, a / 2 - δ ≤ t → t ≤ a / 2 + δ → M / 2 ≤ ψ t := fun t ht1 ht2 => by
    have hd : dist t (a / 2) < δ₁ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) hδ_lt_δ₁
    have hc := hδ₁_close hd
    rw [Real.dist_eq, hψ_mid] at hc
    linarith [(abs_lt.mp hc).1]
  have hq_lt_one : ∀ {t : ℝ}, 0 ≤ t → t ≤ a → t ≠ a / 2 →
      Real.sin (Real.pi * t / a) ^ 2 < 1 := fun {t} ht0 hta htne => by
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * t / a)
    rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · simp
    · rcases eq_or_lt_of_le hta with hta_eq | hta'
      · rw [hta_eq, mul_div_cancel_right₀ Real.pi ha.ne', Real.sin_pi]
        norm_num
      · rcases lt_or_gt_of_ne htne with hlt | hgt
        · have hmem : Real.pi * t / a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
            refine ⟨by linarith [Real.pi_pos, show 0 < Real.pi * t / a by positivity], ?_⟩
            rw [div_lt_iff₀ ha]
            have : Real.pi * t < Real.pi * (a / 2) := mul_lt_mul_of_pos_left hlt Real.pi_pos
            linarith
          have hcos : 0 < Real.cos (Real.pi * t / a) := Real.cos_pos_of_mem_Ioo hmem
          linarith [sq_pos_of_pos hcos]
        · have hmem : Real.pi - Real.pi * t / a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
            refine ⟨?_, ?_⟩
            · have : Real.pi * t / a < Real.pi :=
                (div_lt_iff₀ ha).mpr (mul_lt_mul_of_pos_left hta' Real.pi_pos)
              linarith [Real.pi_pos]
            · have : Real.pi / 2 < Real.pi * t / a := by
                rw [lt_div_iff₀ ha]
                have : Real.pi * (a / 2) < Real.pi * t := mul_lt_mul_of_pos_left hgt Real.pi_pos
                linarith
              linarith
          have hcos' : 0 < Real.cos (Real.pi - Real.pi * t / a) := Real.cos_pos_of_mem_Ioo hmem
          rw [Real.cos_pi_sub] at hcos'
          linarith [sq_pos_of_neg (neg_pos.mp hcos')]
  have hK₁_ne : (Set.Icc (0 : ℝ) (a / 2 - δ)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  have hK₂_ne : (Set.Icc (a / 2 + δ) a).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  obtain ⟨t₁_m, ht₁_m, ht₁_max⟩ :=
    isCompact_Icc.exists_isMaxOn hK₁_ne hq_cont.continuousOn
  obtain ⟨t₂_m, ht₂_m, ht₂_max⟩ :=
    isCompact_Icc.exists_isMaxOn hK₂_ne hq_cont.continuousOn
  set r₀ : ℝ := max (Real.sin (Real.pi * t₁_m / a) ^ 2) (Real.sin (Real.pi * t₂_m / a) ^ 2)
  have hr₀_nonneg : 0 ≤ r₀ := le_trans (sq_nonneg _) (le_max_left _ _)
  have hr₀_lt_one : r₀ < 1 := max_lt
    (hq_lt_one ht₁_m.1 (by linarith [ht₁_m.2]) (by linarith [ht₁_m.2]))
    (hq_lt_one (by linarith [ht₂_m.1]) ht₂_m.2 (by linarith [ht₂_m.1]))
  set r₁ : ℝ := (1 + r₀) / 2 with hr₁_def
  have hr₀_lt_r₁ : r₀ < r₁ := by linarith [hr₁_def]
  have hr₁_pos : 0 < r₁ := by linarith
  have hq_mid : Real.sin (Real.pi * (a / 2) / a) ^ 2 = 1 := by
    have harg : Real.pi * (a / 2) / a = Real.pi / 2 := by field_simp
    simp [harg]
  obtain ⟨η₁, hη₁_pos, hη₁_close⟩ :=
    Metric.continuousAt_iff.mp hq_cont.continuousAt ((1 - r₀) / 2) (by linarith)
  set η : ℝ := min (η₁ / 2) (δ / 2)
  have hη_pos : 0 < η := lt_min (half_pos hη₁_pos) (half_pos hδ_pos)
  have hη_lt_η₁ : η < η₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη₁_pos)
  have hη_le_δ : η ≤ δ := le_trans (min_le_right _ _) (half_le_self hδ_pos.le)
  have hq_ge_r₁ : ∀ t : ℝ, a / 2 - η ≤ t → t ≤ a / 2 + η →
      r₁ ≤ Real.sin (Real.pi * t / a) ^ 2 := fun t ht1 ht2 => by
    have hd : dist t (a / 2) < η₁ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) hη_lt_η₁
    have hc := hη₁_close hd
    dsimp only at hc
    rw [Real.dist_eq, hq_mid] at hc
    linarith [(abs_lt.mp hc).1, hr₁_def]
  have hbound_pow : ∀ m : ℕ, η * (r₁ ^ m * (M / 2)) ≤ a * (r₀ ^ m * M) := fun m => by
    have hintG : ∀ c d : ℝ,
        IntervalIntegrable (fun t => (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) volume c d :=
      fun c d => ((hq_cont.pow m).mul hψ_cont).intervalIntegrable c d
    have hs1 := (intervalIntegral.integral_add_adjacent_intervals
      (hintG 0 (a / 2 - δ)) (hintG (a / 2 - δ) a)).symm
    have hs2 := (intervalIntegral.integral_add_adjacent_intervals
      (hintG (a / 2 - δ) (a / 2 - η)) (hintG (a / 2 - η) a)).symm
    have hs3 := (intervalIntegral.integral_add_adjacent_intervals
      (hintG (a / 2 - η) (a / 2 + η)) (hintG (a / 2 + η) a)).symm
    have hs4 := (intervalIntegral.integral_add_adjacent_intervals
      (hintG (a / 2 + η) (a / 2 + δ)) (hintG (a / 2 + δ) a)).symm
    have hsum0 : (∫ t in (0 : ℝ)..(a / 2 - δ), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) +
        ((∫ t in (a / 2 - δ)..(a / 2 - η), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) +
          ((∫ t in (a / 2 - η)..(a / 2 + η), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) +
            ((∫ t in (a / 2 + η)..(a / 2 + δ), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) +
              (∫ t in (a / 2 + δ)..a, (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t)))) = 0 := by
      rw [← hs4, ← hs3, ← hs2, ← hs1, hint_zero m]
    have hb1 : -((a / 2 - δ) * (r₀ ^ m * M)) ≤
        ∫ t in (0 : ℝ)..(a / 2 - δ), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t := by
      have hm := intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable _ _) (hintG _ _) fun t ht =>
        calc -(r₀ ^ m * M)
            ≤ -((Real.sin (Real.pi * t / a) ^ 2) ^ m * M) :=
              neg_le_neg (mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (sq_nonneg _) (le_trans (ht₁_max ht) (le_max_left _ _)) m) hM)
          _ = (Real.sin (Real.pi * t / a) ^ 2) ^ m * (-M) := by ring
          _ ≤ (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t :=
              mul_le_mul_of_nonneg_left (hψ_abs t) (pow_nonneg (sq_nonneg _) m)
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg] at hm
      exact hm
    have hb2 : 0 ≤ ∫ t in (a / 2 - δ)..(a / 2 - η), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        mul_nonneg (pow_nonneg (sq_nonneg _) m)
          (le_trans (half_pos hM_pos).le (hψ_ge t ht.1 (by linarith [ht.2])))
    have hb3 : (2 * η) * (r₁ ^ m * (M / 2)) ≤
        ∫ t in (a / 2 - η)..(a / 2 + η), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t := by
      have hm := intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable _ _) (hintG _ _) fun t ht =>
        mul_le_mul (pow_le_pow_left₀ hr₁_pos.le (hq_ge_r₁ t ht.1 ht.2) m)
          (hψ_ge t (by linarith [ht.1]) (by linarith [ht.2]))
          (half_pos hM_pos).le (pow_nonneg (sq_nonneg _) m)
      rw [intervalIntegral.integral_const, show (a / 2 + η) - (a / 2 - η) = 2 * η by ring,
        smul_eq_mul] at hm
      exact hm
    have hb4 : 0 ≤ ∫ t in (a / 2 + η)..(a / 2 + δ), (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        mul_nonneg (pow_nonneg (sq_nonneg _) m)
          (le_trans (half_pos hM_pos).le (hψ_ge t (by linarith [ht.1]) ht.2))
    have hb5 : -((a - (a / 2 + δ)) * (r₀ ^ m * M)) ≤
        ∫ t in (a / 2 + δ)..a, (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t := by
      have hm := intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable _ _) (hintG _ _) fun t ht =>
        calc -(r₀ ^ m * M)
            ≤ -((Real.sin (Real.pi * t / a) ^ 2) ^ m * M) :=
              neg_le_neg (mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (sq_nonneg _) (le_trans (ht₂_max ht) (le_max_right _ _)) m) hM)
          _ = (Real.sin (Real.pi * t / a) ^ 2) ^ m * (-M) := by ring
          _ ≤ (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t :=
              mul_le_mul_of_nonneg_left (hψ_abs t) (pow_nonneg (sq_nonneg _) m)
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_neg] at hm
      exact hm
    have hsum_low : -((a - 2 * δ) * (r₀ ^ m * M)) + (2 * η) * (r₁ ^ m * (M / 2)) ≤ 0 := by
      have h1 := add_le_add hb1 (add_le_add hb2 (add_le_add hb3 (add_le_add hb4 hb5)))
      rw [hsum0] at h1
      calc -((a - 2 * δ) * (r₀ ^ m * M)) + (2 * η) * (r₁ ^ m * (M / 2))
          = -((a / 2 - δ) * (r₀ ^ m * M)) +
              (0 + ((2 * η) * (r₁ ^ m * (M / 2)) +
                (0 + -((a - (a / 2 + δ)) * (r₀ ^ m * M))))) := by ring
        _ ≤ _ := h1
    have hA_nonneg : 0 ≤ r₀ ^ m * M := mul_nonneg (pow_nonneg hr₀_nonneg m) hM
    have hB_nonneg : 0 ≤ r₁ ^ m * (M / 2) :=
      mul_nonneg (pow_nonneg hr₁_pos.le m) (half_pos hM_pos).le
    calc η * (r₁ ^ m * (M / 2))
        ≤ (2 * η) * (r₁ ^ m * (M / 2)) := mul_le_mul_of_nonneg_right (by linarith) hB_nonneg
      _ ≤ (a - 2 * δ) * (r₀ ^ m * M) := (neg_add_le_iff_le_add.mp hsum_low).trans_eq (add_zero _)
      _ ≤ a * (r₀ ^ m * M) := mul_le_mul_of_nonneg_right (by linarith) hA_nonneg
  have hratio_le : ∀ m : ℕ, (η * (M / 2)) / (a * M) ≤ (r₀ / r₁) ^ m := fun m => by
    have hm := hbound_pow m
    rw [div_pow, div_le_div_iff₀ (mul_pos ha hM_pos) (pow_pos hr₁_pos m)]
    calc (η * (M / 2)) * r₁ ^ m = η * (r₁ ^ m * (M / 2)) := by ring
      _ ≤ a * (r₀ ^ m * M) := hm
      _ = r₀ ^ m * (a * M) := by ring
  have hratio_lt_one : r₀ / r₁ < 1 := (div_lt_one hr₁_pos).mpr hr₀_lt_r₁
  have htend0 : Tendsto (fun m : ℕ => (r₀ / r₁) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr₀_nonneg hr₁_pos.le) hratio_lt_one
  have hle0 : (η * (M / 2)) / (a * M) ≤ 0 := ge_of_tendsto' htend0 hratio_le
  have hpos : 0 < (η * (M / 2)) / (a * M) := div_pos (mul_pos hη_pos (half_pos hM_pos)) (mul_pos ha hM_pos)
  linarith

private theorem eigenvector_eq_zero_of_pos (B : BorchersPair H)
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
      have hle : θ ≤ Real.pi := Complex.arg_le_pi μ
      have hmul : 2 * Real.pi * (k : ℝ) ≤ -2 * Real.pi := by nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
    · simpa using hθ_ne
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hgt : -Real.pi < θ := Complex.neg_pi_lt_arg μ
      have hmul : 2 * Real.pi ≤ 2 * Real.pi * (k : ℝ) := by nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
  let F : ℤ → ℝ → H := fun k t => Complex.exp (-Complex.I * (ω k : ℂ) * (t : ℂ)) • B.U t w
  have hF_cont : ∀ k : ℤ, Continuous (F k) := fun k => by
    refine Continuous.smul ?_ (B.U_cont w)
    fun_prop
  have hF_per : ∀ k : ℤ, Function.Periodic (F k) a := fun k t => by
    have hUa : B.U (t + a) w = μ • B.U t w := by
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
    rw [intervalIntegral.integral_comp_add_right (fun u => F k u) x, add_comm a x]
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
      refine Eq.trans ?_ h2
      refine intervalIntegral.integral_congr fun t _ => ?_
      change _ = starRingEnd ℂ (Complex.exp (-Complex.I * (α (-k) : ℂ) * (t : ℂ)) * f t)
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp only [α, Int.cast_neg, map_mul, map_neg, conj_I, Complex.conj_ofReal]
      push_cast
      ring
    have hint_f : IntervalIntegrable
        (fun t : ℝ => Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * f t) volume 0 a :=
      (Continuous.mul (by fun_prop) hf_cont).intervalIntegrable 0 a
    have hint_cf : IntervalIntegrable
        (fun t : ℝ => Complex.exp (-Complex.I * (α k : ℂ) * (t : ℂ)) * starRingEnd ℂ (f t))
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
    rw [hrew, intervalIntegral.integral_const_mul, hadd, mul_zero]
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
    rw [Complex.cos]
    have he1 : (2 * (Real.pi : ℂ) * (t : ℂ) / (a : ℂ)) * Complex.I =
        -Complex.I * (α (-1) : ℂ) * (t : ℂ) := by
      simp only [α, Int.cast_neg, Int.cast_one]; push_cast; ring
    have he2 : -(2 * (Real.pi : ℂ) * (t : ℂ) / (a : ℂ)) * Complex.I =
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
          rw [pow_succ', Complex.ofReal_mul, hq_exp t, show k - 1 = k + (-1) from sub_eq_add_neg k 1]
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
  have hreal_int_zero : ∀ m : ℕ,
      (∫ t in (0 : ℝ)..a, (Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t) = 0 := fun m => by
    have h0 := hpow_fourier m 0
    have hα0 : α 0 = 0 := by simp [α]
    have hsimp : (fun t : ℝ => Complex.exp (-Complex.I * (α 0 : ℂ) * (t : ℂ)) *
        (((q t ^ m : ℝ) : ℂ) * (ψ t : ℂ))) =
        fun t : ℝ => (((Real.sin (Real.pi * t / a) ^ 2) ^ m * ψ t : ℝ) : ℂ) := by
      ext t
      rw [hα0]
      simp [q, Complex.ofReal_mul]
    rw [hsimp, intervalIntegral.integral_ofReal] at h0
    exact Complex.ofReal_eq_zero.mp h0
  have hψ_mid : ψ (a / 2) = ‖w‖ ^ 2 := by
    simp only [ψ, f, g₁, F, sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul,
      B.U_zero, one_apply_eq_self]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) w
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
  have hw_sq_le : ‖w‖ ^ 2 ≤ 0 :=
    peaked_integral_pow_zero_imp_le_zero ha (sq_nonneg ‖w‖) hψ_cont hψ_mid hψ_abs hreal_int_zero
  have hw_sq_eq : ‖w‖ ^ 2 = 0 := le_antisymm hw_sq_le (sq_nonneg ‖w‖)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hw_sq_eq)

/-- **No non-identity eigenvectors at nonzero shift.** In any `BorchersPair`, if `a ≠ 0`, `μ ≠ 1`,
and `U(a) w = μ • w`, then `w = 0`. -/
theorem eigenvector_eq_zero_of_ne_one (B : BorchersPair H)
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
theorem trivial_on_finiteDimensional (B : BorchersPair H)
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
    constructor
    · rw [Submodule.mem_orthogonal]
      intro x hx
      have hx' : V_op.symm x = x := V_op.injective (by rw [V_op.apply_symm_apply, (hK_mem x).mp hx])
      calc inner ℂ x (V_op y) = inner ℂ (V_op (V_op.symm x)) (V_op y) := by
            rw [V_op.apply_symm_apply]
        _ = inner ℂ (V_op.symm x) y := V_op.inner_map_map _ _
        _ = inner ℂ x y := by rw [hx']
        _ = 0 := hy x hx
    · rw [Submodule.mem_orthogonal]
      intro x hx
      have hx' : V_op x = x := (hK_mem x).mp hx
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
        change V_op (u : V) = (1 : ℂ) • (u : V) at he
        simpa using he
      have hu0 : (u : V) = 0 := by
        have hu_orth := u.2
        rw [Submodule.mem_orthogonal] at hu_orth
        have hinner : inner ℂ (u : V) (u : V) = 0 := hu_orth (u : V) huK
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
(damped or undamped), if the cyclic subspace generated by a representation `φ` on a vector `Ω` is
invariant under `B.U`, then `B.U` fixes every state `φ(z) Ω` identically. -/
theorem no_nontrivial_borchers_on_quadraticAlgebra (B : BorchersPair H)
    {q t : ℝ} (φ : QuadraticAlgebra ℝ (-q) t →ₐ[ℝ] H →L[ℂ] H) (Ω : H)
    (hinv : ∀ (a : ℝ) (z : QuadraticAlgebra ℝ (-q) t),
      B.U a (φ z Ω) ∈ Submodule.span ℂ ({Ω, φ QuadraticAlgebra.omega Ω} : Set H))
    (a : ℝ) (z : QuadraticAlgebra ℝ (-q) t) :
    B.U a (φ z Ω) = φ z Ω := by
  set V : Submodule ℂ H := Submodule.span ℂ ({Ω, φ QuadraticAlgebra.omega Ω} : Set H)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hr_smul : ∀ (r : ℝ) (v : H), r • v = (r : ℂ) • v := fun r v => by
    calc r • v = r • ((1 : ℂ) • v) := by rw [one_smul]
      _ = (r • (1 : ℂ)) • v := (smul_assoc r (1 : ℂ) v).symm
      _ = ((r : ℂ) * 1) • v := by rw [Complex.real_smul]
      _ = (r : ℂ) • v := by rw [mul_one]
  have hz_mem : ∀ w : QuadraticAlgebra ℝ (-q) t, φ w Ω ∈ V := fun w => by
    have hw_eq : w = algebraMap ℝ _ w.re + w.im • QuadraticAlgebra.omega := by
      ext <;> simp [QuadraticAlgebra.omega]
    have hφw : φ w Ω = (w.re : ℂ) • Ω + (w.im : ℂ) • (φ QuadraticAlgebra.omega Ω) := by
      rw [hw_eq, map_add, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul]
      change w.re • Ω + w.im • (φ QuadraticAlgebra.omega Ω) = _
      rw [hr_smul, hr_smul]
    rw [hφw]
    exact add_mem (V.smul_mem _ (Submodule.subset_span (by simp)))
      (V.smul_mem _ (Submodule.subset_span (by simp)))
  have hV_inv : ∀ (b : ℝ), ∀ v ∈ V, B.U b v ∈ V := fun b v hv => by
    refine Submodule.span_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => by rw [map_add]; exact add_mem hx hy)
      (fun c x _ hx => by rw [map_smul]; exact V.smul_mem c hx) hv
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · simpa [map_one] using hinv b 1
    · rw [Set.mem_singleton_iff.mp hx']
      exact hinv b QuadraticAlgebra.omega
  exact B.trivial_on_finiteDimensional V hV_inv a (hz_mem z)

/-- **Triviality of antiperiodic vectors.** In any `BorchersPair`, `U(τ) w = -w` (`τ ≠ 0`) forces
`w = 0`. -/
theorem antiperiodic_eq_zero (B : BorchersPair H)
    {τ : ℝ} (hτ : τ ≠ 0) {w : H} (hw : B.U τ w = -w) : w = 0 :=
  B.eigenvector_eq_zero_of_ne_one hτ (by norm_num : (-1 : ℂ) ≠ 1) (by simpa using hw)

/-- **Vanishing of alternating Cesàro Bohr averages.** For every nonzero frequency `γ ≠ 0` and
every vector `ψ ∈ H`, `(1 / K) ∑_{k < K} (-1)^k ⟪ψ, U(k π / γ) ψ⟫ → 0` as `K → ∞`. -/
theorem alternating_cesaro_tendsto_zero (B : BorchersPair H)
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
        rw [pow_succ']
        change -(B.U τ ((W ^ k) v)) = _
        rw [ih v, map_smul, ← smul_neg]
        have hstep : -(B.U τ (B.U ((k : ℝ) * τ) v)) = (-1 : ℂ) • B.U (((k + 1 : ℕ) : ℝ) * τ) v := by
          rw [neg_one_smul]
          congr 1
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm ((k : ℝ) * τ) τ, B.U_add]
          rfl
        rw [hstep, smul_smul, pow_succ]
  have hW_norm : ∀ (k : ℕ) (v : H), ‖(W ^ k) v‖ = ‖v‖ := fun k v => by
    rw [hW_pow k v, norm_smul, _root_.norm_pow, norm_neg, norm_one, one_pow, one_mul, B.norm_U]
  let R : Submodule ℂ H := LinearMap.range ((W - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)
  have hR_perp : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [Submodule.mem_orthogonal] at hz
    have hadj0 : (star (W - 1 : H →L[ℂ] H)) z = 0 := by
      have hself : inner ℂ ((W - 1 : H →L[ℂ] H) ((star (W - 1 : H →L[ℂ] H)) z)) z = 0 :=
        hz _ ⟨(star (W - 1 : H →L[ℂ] H)) z, rfl⟩
      rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_inner_right] at hself
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact inner_self_eq_zero.mp hself
    have hanti : B.U (-τ) z = -z := by
      have hstarW : star (W - 1 : H →L[ℂ] H) = -B.U (-τ) - 1 := by
        simp only [W, star_sub, star_one, star_neg, B.star_U]
      rw [hstarW] at hadj0
      change -(B.U (-τ) z) - z = 0 at hadj0
      exact neg_eq_iff_eq_neg.mp (sub_eq_zero.mp hadj0)
    exact B.antiperiodic_eq_zero (neg_ne_zero.mpr hτ) hanti
  have hR_dense : ∀ δ > 0, ∃ x : H, ‖ψ - (W - 1) x‖ < δ := by
    intro δ hδ
    have hcl_top : R.topologicalClosure = ⊤ := by
      have hp : R.topologicalClosureᗮ = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro z hz
        rw [Submodule.mem_orthogonal] at hz
        have hzR : z ∈ Rᗮ := by
          rw [Submodule.mem_orthogonal]
          exact fun y hy => hz y (subset_closure hy)
        rwa [hR_perp, Submodule.mem_bot] at hzR
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
          change (W ^ K) (W x - x) = _
          rw [map_sub, pow_succ]
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

/-! ### 4. Unconditional impossibility over `ℤ` and partner standard-form trichotomy -/

/-- The positive integer `n + 1 : ℕ+` attached to `n : ℕ`. -/
def natPNat (n : ℕ) : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩

@[simp] theorem coe_natPNat_real (n : ℕ) : ((natPNat n : ℕ+) : ℝ) = (n : ℝ) + 1 := by
  simp [natPNat]

/-- Any homogeneous degree-2 functional equals its quadratic Tate limit everywhere. -/
theorem eq_of_quadratic_tateLimit {M : Type*} [AddCommMonoid M] {F : M → ℝ}
    (hsmul : ∀ (m : ℕ) (a : M), F (m • a) = (m : ℝ) ^ 2 * F a) {a : M} {Q : ℝ}
    (htend : Tendsto (fun m : ℕ => F (m • a) / (m : ℝ) ^ 2) atTop (𝓝 Q)) :
    F a = Q := by
  have hev : (fun m : ℕ => F (m • a) / (m : ℝ) ^ 2) =ᶠ[atTop] fun _ : ℕ => F a := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ^ 2 ≠ 0 := by positivity
    rw [hsmul, mul_div_cancel_left₀ _ hm0]
  exact tendsto_nhds_unique (htend.congr' hev) tendsto_const_nhds

/-- Two symmetric real kernels agreeing as quadratic forms on `ℤ^N` agree entrywise. -/
private theorem eq_of_symm_intQuad_eq {N : ℕ} {C₁ C₂ : Fin N → Fin N → ℝ}
    (hs₁ : ∀ i j, C₁ i j = C₁ j i) (hs₂ : ∀ i j, C₂ i j = C₂ j i)
    (hq : ∀ a : Fin N → ℤ,
      (∑ i : Fin N, ∑ j : Fin N, C₁ i j * (a i : ℝ) * (a j : ℝ)) =
        ∑ i : Fin N, ∑ j : Fin N, C₂ i j * (a i : ℝ) * (a j : ℝ))
    (i₀ j₀ : Fin N) : C₁ i₀ j₀ = C₂ i₀ j₀ := by
  set D : Fin N → Fin N → ℝ := fun i j => C₁ i j - C₂ i j
  have hDs : ∀ i j, D i j = D j i := fun i j => by simp only [D, hs₁ i j, hs₂ i j]
  have hD0 : ∀ a : Fin N → ℤ, ∑ i : Fin N, ∑ j : Fin N, D i j * (a i : ℝ) * (a j : ℝ) = 0 := by
    intro a
    have hsub : (∑ i : Fin N, ∑ j : Fin N, D i j * (a i : ℝ) * (a j : ℝ)) =
        (∑ i : Fin N, ∑ j : Fin N, C₁ i j * (a i : ℝ) * (a j : ℝ)) -
          ∑ i : Fin N, ∑ j : Fin N, C₂ i j * (a i : ℝ) * (a j : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [D]; ring
    rw [hsub, hq a, sub_self]
  set x : Fin N → ℤ := Pi.single i₀ 1
  set y : Fin N → ℤ := Pi.single j₀ 1
  have hpol : 2 * (∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (y j : ℝ)) =
      (∑ i : Fin N, ∑ j : Fin N, D i j * (((x + y) i : ℤ) : ℝ) * (((x + y) j : ℤ) : ℝ)) -
        (∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (x j : ℝ)) -
          (∑ i : Fin N, ∑ j : Fin N, D i j * (y i : ℝ) * (y j : ℝ)) := by
    have hswap : (∑ i : Fin N, ∑ j : Fin N, D i j * (y i : ℝ) * (x j : ℝ)) =
        ∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (y j : ℝ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hDs j i]; ring
    have hexp : (∑ i : Fin N, ∑ j : Fin N, D i j * (((x + y) i : ℤ) : ℝ) * (((x + y) j : ℤ) : ℝ)) =
        (∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (x j : ℝ)) +
          (∑ i : Fin N, ∑ j : Fin N, D i j * (y i : ℝ) * (y j : ℝ)) +
            (∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (y j : ℝ)) +
              (∑ i : Fin N, ∑ j : Fin N, D i j * (y i : ℝ) * (x j : ℝ)) := by
      simp only [← Finset.sum_add_distrib, Pi.add_apply, Int.cast_add]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, hswap]
    ring
  rw [hD0 (x + y), hD0 x, hD0 y] at hpol
  have hbl0 : ∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (y j : ℝ) = 0 := by linarith
  have heval : (∑ i : Fin N, ∑ j : Fin N, D i j * (x i : ℝ) * (y j : ℝ)) = D i₀ j₀ := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single j₀]
      · simp [x, y]
      · intro j _ hj; simp [y, Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ j₀) h
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => by simp [x, Pi.single_eq_of_ne hi]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [heval] at hbl0
  exact sub_eq_zero.mp hbl0

private theorem atomGram_eq_splineCorr (N : ℕ) (i j : Fin N) :
    atomGram N i j = splineCorr (Real.log (((i : ℝ) + 1) / ((j : ℝ) + 1))) := by
  have h1 : atomGram N i j = splineCorr (Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1)) :=
    weilGram_translate_cubicSpline (fun k : Fin N => Real.log ((k : ℝ) + 1)) i j
  rw [h1, Real.log_div (by positivity) (by positivity)]

private theorem atomGram_re_symm (N : ℕ) (i j : Fin N) :
    (atomGram N i j).re = (atomGram N j i).re := by
  have hH : starRingEnd ℂ (atomGram N j i) = atomGram N i j :=
    congr_fun (congr_fun (atomGram_isHermitian N) i) j
  have hre := congr_arg Complex.re hH
  simpa using hre.symm

private theorem integerProbe_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    integerProbe N a = ∑ i : Fin N, ∑ j : Fin N, (atomGram N i j).re * (a i : ℝ) * (a j : ℝ) := by
  unfold integerProbe HTGeometry.hermQuad
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, conj_intCast,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hreal : atomGram N i j = ((atomGram N i j).re : ℂ) :=
    Complex.ext rfl (by simpa using atomGram_im N i j)
  rw [hreal]
  have hcast : (a i : ℂ) * (((atomGram N i j).re : ℂ) * (a j : ℂ)) =
      (((atomGram N i j).re * (a i : ℝ) * (a j : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- Any symmetric real kernel on `ℕ+ × ℕ+` whose finite quadratic forms over `ℤ` match `integerProbe`
equals `splineCorr(log(m / n))` at every pair `(m, n) ∈ ℕ+ × ℕ+`. -/
theorem symmKernel_eq_splineCorr_of_integerProbe {C : ℕ+ → ℕ+ → ℝ}
    (hsym : ∀ m n : ℕ+, C m n = C n m)
    (hprobe : ∀ (N : ℕ) (a : Fin N → ℤ),
      (∑ i : Fin N, ∑ j : Fin N, C (natPNat i) (natPNat j) * (a i : ℝ) * (a j : ℝ)) =
        integerProbe N a)
    (m n : ℕ+) :
    C m n = (splineCorr (Real.log ((m : ℝ) / (n : ℝ)))).re ∧
      splineCorr (Real.log ((m : ℝ) / (n : ℝ))) = (C m n : ℂ) := by
  let N : ℕ := max (m : ℕ) (n : ℕ)
  have hmN : (m : ℕ) - 1 < N := by
    have hm0 : 0 < (m : ℕ) := m.pos
    have hle : (m : ℕ) ≤ N := le_max_left _ _
    omega
  have hnN : (n : ℕ) - 1 < N := by
    have hn0 : 0 < (n : ℕ) := n.pos
    have hle : (n : ℕ) ≤ N := le_max_right _ _
    omega
  let i₀ : Fin N := ⟨(m : ℕ) - 1, hmN⟩
  let j₀ : Fin N := ⟨(n : ℕ) - 1, hnN⟩
  have hi₀ : natPNat i₀ = m := by
    apply Subtype.ext
    show ((m : ℕ) - 1) + 1 = (m : ℕ)
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt m.pos)
  have hj₀ : natPNat j₀ = n := by
    apply Subtype.ext
    show ((n : ℕ) - 1) + 1 = (n : ℕ)
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)
  have hi₀_r : (i₀ : ℝ) + 1 = (m : ℝ) := by
    have h := congr_arg (fun x : ℕ+ => (x : ℝ)) hi₀
    simpa [natPNat] using h
  have hj₀_r : (j₀ : ℝ) + 1 = (n : ℝ) := by
    have h := congr_arg (fun x : ℕ+ => (x : ℝ)) hj₀
    simpa [natPNat] using h
  have heq_entry : C (natPNat i₀) (natPNat j₀) = (atomGram N i₀ j₀).re :=
    eq_of_symm_intQuad_eq (fun i j => hsym _ _) (atomGram_re_symm N)
      (fun a => (hprobe N a).trans (integerProbe_eq_sum N a)) i₀ j₀
  rw [hi₀, hj₀] at heq_entry
  have hgram : atomGram N i₀ j₀ = splineCorr (Real.log ((m : ℝ) / (n : ℝ))) := by
    rw [atomGram_eq_splineCorr N i₀ j₀, hi₀_r, hj₀_r]
  have him : (splineCorr (Real.log ((m : ℝ) / (n : ℝ)))).im = 0 := by
    rw [← hgram]
    exact atomGram_im N i₀ j₀
  have hre : C m n = (splineCorr (Real.log ((m : ℝ) / (n : ℝ)))).re := by
    rwa [hgram] at heq_entry
  exact ⟨hre, Complex.ext hre.symm (by simpa using him)⟩

/-- **Unconditional cross-horizon natural-cone impossibility.** No standard-form von Neumann algebra
`(H, M, ms)` equipped with a vacuum-fixing multiplicative isometric partner representation
`U : ℕ+ → H →L[ℂ] H` (`U(n) Ω = Ω`, `J U(n) J = U(n)*`) and a seed operator `A₀` has cross-horizon
natural-cone form on `X(a) = ∑_{i < N} a_i U(i + 1) A₀ U(i + 1)*` with Tate limit `integerProbe`. -/
theorem no_vacuumFixing_partner_tateLimit_integerProbe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (ms : StandardForm M) {U : ℕ+ → H →L[ℂ] H}
    (hmul : ∀ m n : ℕ+, U (m * n) = U m * U n)
    (hiso : ∀ n : ℕ+, star (U n) * U n = 1)
    (hΩ : ∀ n : ℕ+, U n ms.Ω = ms.Ω)
    (hJ : ∀ n : ℕ+, ms.J.conjOp (U n) = star (U n))
    (A₀ : H →L[ℂ] H)
    (htate : ∀ (N : ℕ) (a : Fin N → ℤ),
      Tendsto (fun m : ℕ =>
        (let X : H →L[ℂ] H := ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift U (natPNat i) A₀
         (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re) / (m : ℝ) ^ 2)
        atTop (𝓝 (integerProbe N a))) :
    False := by
  set g : ℕ+ → ℝ := fun k => (inner ℂ ((star A₀) ms.Ω) ((star (U k)) (ms.J (A₀ ms.Ω)))).re
  set C : ℕ+ → ℕ+ → ℝ := fun m n => g (m * n)
  have hsym : ∀ m n : ℕ+, C m n = C n m := fun m n => by simp only [C, mul_comm]
  have hquad_exp : ∀ (N : ℕ) (a : Fin N → ℤ),
      (let X : H →L[ℂ] H := ∑ i : Fin N, (a i : ℂ) • covShift U (natPNat i) A₀
       (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re) =
        ∑ i : Fin N, ∑ j : Fin N, C (natPNat i) (natPNat j) * (a i : ℝ) * (a j : ℝ) := by
    intro N a
    set X : H →L[ℂ] H := ∑ i : Fin N, (a i : ℂ) • covShift U (natPNat i) A₀
    have hJX : ms.J.conjOp X ms.Ω =
        ∑ j : Fin N, (a j : ℂ) • (ms.J.conjOp (covShift U (natPNat j) A₀) ms.Ω) := by
      simp only [X, AntiunitaryInvol.conjOp_sum, AntiunitaryInvol.conjOp_smul, conj_intCast,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    have hXJX : X (ms.J.conjOp X ms.Ω) =
        ∑ i : Fin N, ∑ j : Fin N,
          ((a i : ℂ) * (a j : ℂ)) •
            (covShift U (natPNat i) A₀ (ms.J.conjOp (covShift U (natPNat j) A₀) ms.Ω)) := by
      rw [hJX]
      simp only [X, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        map_sum, map_smul, Finset.smul_sum, smul_smul]
    change (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re = _
    rw [hXJX, inner_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, ms.naturalCone_partner_hankel hmul hiso hΩ hJ A₀ A₀ (natPNat i) (natPNat j)]
    have hre_mul : (((a i : ℂ) * (a j : ℂ)) *
        inner ℂ ((star A₀) ms.Ω) ((star (U (natPNat i * natPNat j))) (ms.J (A₀ ms.Ω)))).re =
        g (natPNat i * natPNat j) * (a i : ℝ) * (a j : ℝ) := by
      have hcast : (a i : ℂ) * (a j : ℂ) = (((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.re_ofReal_mul]
      simp only [g]
      ring
    exact hre_mul
  have hprobe : ∀ (N : ℕ) (a : Fin N → ℤ),
      (∑ i : Fin N, ∑ j : Fin N, C (natPNat i) (natPNat j) * (a i : ℝ) * (a j : ℝ)) =
        integerProbe N a := by
    intro N a
    set FN : (Fin N → ℤ) → ℝ := fun b =>
      ∑ i : Fin N, ∑ j : Fin N, C (natPNat i) (natPNat j) * (b i : ℝ) * (b j : ℝ)
    have hsmul : ∀ (m : ℕ) (b : Fin N → ℤ), FN (m • b) = (m : ℝ) ^ 2 * FN b := fun m b => by
      simp only [FN, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have htend' : Tendsto (fun m : ℕ => FN (m • a) / (m : ℝ) ^ 2) atTop (𝓝 (integerProbe N a)) := by
      simpa only [hquad_exp N] using htate N a
    exact eq_of_quadratic_tateLimit hsmul htend'
  have hspline_hankel : ∀ m n : ℕ+,
      splineCorr (Real.log ((m : ℝ) / (n : ℝ))) = (g (m * n) : ℂ) := fun m n =>
    (symmKernel_eq_splineCorr_of_integerProbe hsym hprobe m n).2
  have hconst : ∀ y : ℝ, splineCorr y = splineCorr 0 :=
    const_of_mulHankel_eq_logToeplitz continuous_splineCorr hspline_hankel
  obtain ⟨u, _, v, _, hne⟩ := exists_coprimeCrossDiff_ratCorr_ne_zero
  apply hne
  simp only [AdelicKreinGeometry.coprimeCrossDiff, ratCorr, hconst]
  ring

/-- Exact cross-horizon Born-rule corollary of `no_vacuumFixing_partner_tateLimit_integerProbe`. -/
theorem no_vacuumFixing_partner_bornRule_integerProbe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (ms : StandardForm M) {U : ℕ+ → H →L[ℂ] H}
    (hmul : ∀ m n : ℕ+, U (m * n) = U m * U n)
    (hiso : ∀ n : ℕ+, star (U n) * U n = 1)
    (hΩ : ∀ n : ℕ+, U n ms.Ω = ms.Ω)
    (hJ : ∀ n : ℕ+, ms.J.conjOp (U n) = star (U n))
    (A₀ : H →L[ℂ] H)
    (hborn : ∀ (N : ℕ) (a : Fin N → ℤ),
      let X : H →L[ℂ] H := ∑ i : Fin N, (a i : ℂ) • covShift U (natPNat i) A₀
      (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re = integerProbe N a) :
    False := by
  refine no_vacuumFixing_partner_tateLimit_integerProbe ms hmul hiso hΩ hJ A₀ fun N a => ?_
  have hev : (fun m : ℕ =>
      (let X : H →L[ℂ] H := ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift U (natPNat i) A₀
       (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re) / (m : ℝ) ^ 2) =ᶠ[atTop]
      fun _ : ℕ => integerProbe N a := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ^ 2 ≠ 0 := by positivity
    rw [hborn N (m • a), integerProbe_smul, mul_div_cancel_left₀ _ hm0]
  exact tendsto_const_nhds.congr' hev.symm

/-- **Unconditional Borchers one-sided GNS / Lax–Phillips impossibility.** No `BorchersPair H` and
seed vector `ψ₀ ∈ H` satisfy `‖∑_{i < N} (m a_i) U(log(i + 1)) ψ₀‖² / m² → integerProbe N a` for all
finite integer probes: positivity forces `RiemannHypothesis`, turning `splineCorr` into an atomic
critical-line Bohr series whose alternating Cesàro average at any seen critical zero is strictly
positive against `BorchersPair.alternating_cesaro_tendsto_zero`. -/
theorem no_borchers_gns_tateLimit_integerProbe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : BorchersPair H) (ψ₀ : H)
    (htate : ∀ (N : ℕ) (a : Fin N → ℤ),
      Tendsto (fun m : ℕ =>
        ‖∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀‖ ^ 2 / (m : ℝ) ^ 2)
        atTop (𝓝 (integerProbe N a))) :
    False := by
  classical
  have hnorm_eq : ∀ (N : ℕ) (a : Fin N → ℤ),
      ‖∑ i : Fin N, (a i : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀‖ ^ 2 = integerProbe N a := by
    intro N a
    set GN : (Fin N → ℤ) → ℝ := fun b =>
      ‖∑ i : Fin N, (b i : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀‖ ^ 2
    have hsmul : ∀ (m : ℕ) (b : Fin N → ℤ), GN (m • b) = (m : ℝ) ^ 2 * GN b := fun m b => by
      have hvec : (∑ i : Fin N, (((m • b) i : ℤ) : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀) =
          (m : ℂ) • ∑ i : Fin N, (b i : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀ := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [smul_smul]
      simp only [GN, hvec, norm_smul, Complex.norm_natCast, mul_pow]
    exact eq_of_quadratic_tateLimit hsmul (htate N a)
  have hRH : RiemannHypothesis :=
    riemannHypothesis_iff_integerProbes.mpr fun N a => by
      rw [← hnorm_eq N a]
      exact sq_nonneg _
  set c : ℝ → ℝ := fun y => (inner ℂ ψ₀ (B.U y ψ₀)).re
  have hc_even : ∀ y : ℝ, c (-y) = c y := fun y => by
    have h1 : inner ℂ ψ₀ (B.U (-y) ψ₀) = starRingEnd ℂ (inner ℂ ψ₀ (B.U y ψ₀)) := by
      calc inner ℂ ψ₀ (B.U (-y) ψ₀)
          = inner ℂ (B.U y ψ₀) (B.U y (B.U (-y) ψ₀)) := (B.inner_U y _ _).symm
        _ = inner ℂ (B.U y ψ₀) ((B.U y * B.U (-y)) ψ₀) := rfl
        _ = inner ℂ (B.U y ψ₀) ψ₀ := by rw [B.U_mul_neg]; rfl
        _ = starRingEnd ℂ (inner ℂ ψ₀ (B.U y ψ₀)) := (inner_conj_symm _ _).symm
    simpa only [c, Complex.conj_re] using congr_arg Complex.re h1
  set C : ℕ+ → ℕ+ → ℝ := fun m n => c (Real.log ((m : ℝ) / (n : ℝ)))
  have hCsym : ∀ m n : ℕ+, C m n = C n m := fun m n => by
    have hlog : Real.log ((n : ℝ) / (m : ℝ)) = -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]
      ring
    simp only [C, hlog, hc_even]
  have hCprobe : ∀ (N : ℕ) (a : Fin N → ℤ),
      (∑ i : Fin N, ∑ j : Fin N, C (natPNat i) (natPNat j) * (a i : ℝ) * (a j : ℝ)) =
        integerProbe N a := by
    intro N a
    rw [← hnorm_eq N a]
    set v : H := ∑ i : Fin N, (a i : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀
    have hv_sq : ‖v‖ ^ 2 = (inner ℂ v v).re := (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm
    rw [hv_sq]
    simp only [v, sum_inner, inner_sum, Complex.re_sum]
    symm
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, conj_intCast, ← mul_assoc]
    have hshift : inner ℂ (B.U (Real.log ((i : ℝ) + 1)) ψ₀) (B.U (Real.log ((j : ℝ) + 1)) ψ₀) =
        inner ℂ ψ₀ (B.U (Real.log ((j : ℝ) + 1) - Real.log ((i : ℝ) + 1)) ψ₀) := by
      calc inner ℂ (B.U (Real.log ((i : ℝ) + 1)) ψ₀) (B.U (Real.log ((j : ℝ) + 1)) ψ₀)
          = inner ℂ (B.U (-Real.log ((i : ℝ) + 1)) (B.U (Real.log ((i : ℝ) + 1)) ψ₀))
              (B.U (-Real.log ((i : ℝ) + 1)) (B.U (Real.log ((j : ℝ) + 1)) ψ₀)) :=
            (B.inner_U (-Real.log ((i : ℝ) + 1)) _ _).symm
        _ = inner ℂ ((B.U (-Real.log ((i : ℝ) + 1)) * B.U (Real.log ((i : ℝ) + 1))) ψ₀)
              ((B.U (-Real.log ((i : ℝ) + 1)) * B.U (Real.log ((j : ℝ) + 1))) ψ₀) := rfl
        _ = inner ℂ ψ₀ (B.U (-Real.log ((i : ℝ) + 1) + Real.log ((j : ℝ) + 1)) ψ₀) := by
            rw [B.U_neg_mul, ← B.U_add]; rfl
        _ = inner ℂ ψ₀ (B.U (Real.log ((j : ℝ) + 1) - Real.log ((i : ℝ) + 1)) ψ₀) := by
            rw [sub_eq_add_neg, add_comm]
    have hcast : (a i : ℂ) * (a j : ℂ) = (((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hshift, hcast, Complex.re_ofReal_mul]
    have harg : Real.log ((j : ℝ) + 1) - Real.log ((i : ℝ) + 1) =
        -Real.log (((natPNat i : ℕ+) : ℝ) / ((natPNat j : ℕ+) : ℝ)) := by
      rw [coe_natPNat_real, coe_natPNat_real, Real.log_div (by positivity) (by positivity)]
      ring
    change ((a i : ℝ) * (a j : ℝ)) * c (Real.log ((j : ℝ) + 1) - Real.log ((i : ℝ) + 1)) = _
    rw [harg, hc_even]
    simp only [C]
    ring
  have hc_cont : Continuous c :=
    Complex.continuous_re.comp ((continuous_const : Continuous fun _ : ℝ => ψ₀).inner (B.U_cont ψ₀))
  have hc_eq_spline : ∀ y : ℝ, c y = (splineCorr y).re := by
    intro y
    have hcl : IsClosed {t : ℝ | c t = (splineCorr t).re} :=
      isClosed_eq hc_cont (Complex.continuous_re.comp continuous_splineCorr)
    refine (hcl.closure_subset_iff.mpr ?_) (dense_mul_log_pnat_div one_ne_zero y)
    rintro _ ⟨m, n, rfl⟩
    rw [one_mul]
    exact (symmKernel_eq_splineCorr_of_integerProbe hCsym hCprobe m n).1
  -- Under RH, `splineCorr` is the critical-line Bohr series on `ℝ`.
  obtain ⟨e⟩ := exists_enum_onLine
  have hR_empty : rightZeros zetaZeroConfig = ∅ :=
    ArithmeticOrientationGeometry.riemannHypothesis_iff_no_rightZero.mp hRH
  have hR : (rightZeros zetaZeroConfig).Finite := hR_empty ▸ Set.finite_empty
  have hR_fin : hR.toFinset = ∅ := by ext ρ; simp [hR_empty]
  set bohrReal : ℝ → ℂ := fun y =>
    ∑' j : ℕ, (onLineWeight e j : ℂ) *
      Complex.exp (Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (y : ℂ))
  have hw_nonneg : ∀ j : ℕ, 0 ≤ onLineWeight e j := fun j => by
    rw [onLineWeight, Wsummand_onLine (e j).2, Complex.ofReal_re]
    positivity
  have hexp_norm : ∀ (θ : ℝ), ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := fun θ => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hbohr_cont : Continuous bohrReal := by
    refine continuous_tsum (fun j => by fun_prop) (summable_onLineWeight e) fun j y => ?_
    have hexp1 : ‖Complex.exp (Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (y : ℂ))‖ = 1 := by
      have harg : Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (y : ℂ) =
          Complex.I * ((((e j : ℂ).im * y : ℝ) : ℂ)) := by push_cast; ring
      rw [harg, hexp_norm]
    rw [norm_mul, hexp1, mul_one, Complex.norm_real, Real.norm_of_nonneg (hw_nonneg j)]
  have hspline_bohr_rat : ∀ m n : ℕ+,
      splineCorr (Real.log ((m : ℝ) / (n : ℝ))) = bohrReal (Real.log ((m : ℝ) / (n : ℝ))) := by
    intro m n
    let u : posUnits := (natPosUnit ((m : ℕ) - 1))⁻¹ * natPosUnit ((n : ℕ) - 1)
    have hm_sub : (((m : ℕ) - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt m.pos)
    have hn_sub : (((n : ℕ) - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)
    have hlog_u : logPos u = -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [logPos_inv_mul, logPos_natPosUnit, logPos_natPosUnit, hm_sub, hn_sub,
        Real.log_div (by positivity) (by positivity)]
      ring
    have hcorr_u : splineCorr (Real.log ((m : ℝ) / (n : ℝ))) = ratCorr u := by
      simp [ratCorr, hlog_u]
    rw [hcorr_u, ratCorr_eq_zetaKernel, zetaKernel,
      orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig
        HeckeKreinToeplitz.cubicSpline_mem_realTests hR (posUnitsToHecke u),
      hR_fin, Finset.sum_empty, add_zero,
      congr_fun (orbitKernel_onLine_eq_bohrSum e) (posUnitsToHecke u)]
    unfold HeckeKreinToeplitz.bohrSum bohrReal
    refine tsum_congr fun j => ?_
    congr 1
    rw [onLineChar, logChar_apply]
    have hsc : HeckeKreinToeplitz.scale heckeLogScale (posUnitsToHecke u) = logPos u := rfl
    rw [hsc, hlog_u]
    congr 1
    push_cast
    ring
  have hspline_eq_bohr : ∀ y : ℝ, splineCorr y = bohrReal y := by
    intro y
    have hcl : IsClosed {t : ℝ | splineCorr t = bohrReal t} :=
      isClosed_eq continuous_splineCorr hbohr_cont
    refine (hcl.closure_subset_iff.mpr ?_) (dense_mul_log_pnat_div one_ne_zero y)
    rintro _ ⟨m, n, rfl⟩
    rw [one_mul]
    exact hspline_bohr_rat m n
  -- Choose a seen critical zero `ρ₀ ≠ 1/2`, so `γ₀ := ρ₀.im ≠ 0` and `onLineWeight e j₀ > 0`.
  obtain ⟨ρ₀, hρ₀_seen, hρ₀_ne⟩ :=
    (criticalSeen_infinite.diff (Set.finite_singleton (1 / 2 : ℂ))).nonempty
  set γ₀ : ℝ := ρ₀.im
  have hγ₀ : γ₀ ≠ 0 := by
    intro h0
    apply hρ₀_ne
    rw [Set.mem_singleton_iff]
    exact Complex.ext hρ₀_seen.2.1 (by simpa [γ₀] using h0)
  let j₀ : ℕ := e.symm ⟨ρ₀, criticalSeen_subset hρ₀_seen⟩
  have he_j₀ : (e j₀ : ℂ) = ρ₀ := congr_arg Subtype.val (e.apply_symm_apply _)
  have hw_j₀_pos : 0 < onLineWeight e j₀ := by
    have hs := criticalSeen_subset hρ₀_seen
    simp only [j₀, onLineWeight, Equiv.apply_symm_apply, Wsummand_onLine hs, Complex.ofReal_re]
    have hm : (1 : ℝ) ≤ zetaOnLine.mult ρ₀ := by exact_mod_cast zetaOnLine.one_le_mult ρ₀ hs
    have hF : 0 < ‖Zeta23.paperFT (cx cubicSpline) (ρ₀.im : ℂ)‖ := norm_pos_iff.mpr hρ₀_seen.2.2
    positivity
  set τ : ℝ := Real.pi / γ₀
  set z : ℕ → ℂ := fun j =>
    -Complex.exp (Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (τ : ℂ))
  have hz_norm : ∀ j : ℕ, ‖z j‖ = 1 := fun j => by
    have harg : Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (τ : ℂ) =
        Complex.I * ((((e j : ℂ).im * τ : ℝ) : ℂ)) := by push_cast; ring
    rw [norm_neg, harg, hexp_norm]
  have hz_j₀ : z j₀ = 1 := by
    have him : (e j₀ : ℂ).im = γ₀ := by rw [he_j₀]
    have harg : Complex.I * (((e j₀ : ℂ).im : ℝ) : ℂ) * (τ : ℂ) = (Real.pi : ℂ) * Complex.I := by
      rw [him]
      simp only [τ, Complex.ofReal_div]
      have hne : (γ₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ₀
      field_simp [hne]
    simp only [z, harg, Complex.exp_pi_mul_I, neg_neg]
  set avg : ℕ → ℕ → ℂ := fun K j => (∑ k ∈ Finset.range K, z j ^ k) / (K : ℂ)
  have havg_norm : ∀ (K j : ℕ), ‖avg K j‖ ≤ 1 := by
    intro K j
    rcases eq_or_ne K 0 with rfl | hK
    · simp [avg]
    · have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hK)
      rw [ norm_div, Complex.norm_natCast, div_le_one hK_pos]
      calc ‖∑ k ∈ Finset.range K, z j ^ k‖
          ≤ ∑ k ∈ Finset.range K, ‖z j ^ k‖ := norm_sum_le _ _
        _ = ∑ _ ∈ Finset.range K, (1 : ℝ) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [_root_.norm_pow, hz_norm j, one_pow]
        _ = (K : ℝ) := by simp
  have havg_tendsto : ∀ j : ℕ,
      Tendsto (fun K : ℕ => avg K j) atTop (𝓝 (if z j = 1 then (1 : ℂ) else 0)) := by
    intro j
    by_cases hz1 : z j = 1
    · rw [if_pos hz1]
      have hev : (fun K : ℕ => avg K j) =ᶠ[atTop] fun _ : ℕ => (1 : ℂ) := by
        filter_upwards [eventually_ge_atTop 1] with K hK
        have hK0 : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp [avg, hz1, div_self hK0]
      exact tendsto_const_nhds.congr' hev.symm
    · rw [if_neg hz1]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hdenom : 0 < ‖z j - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
      have hbound : ∀ K : ℕ, ‖avg K j‖ ≤ (2 / ‖z j - 1‖) * ((K : ℝ))⁻¹ := by
        intro K
        rcases eq_or_ne K 0 with rfl | hK
        · simp [avg]
        · rw [avg, geom_sum_eq hz1 K, norm_div, norm_div, Complex.norm_natCast, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hdenom.le) (by positivity)
          calc ‖z j ^ K - 1‖ ≤ ‖z j ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [_root_.norm_pow, hz_norm j, one_pow, norm_one]; norm_num
      have htend_inv : Tendsto (fun K : ℕ => (2 / ‖z j - 1‖) * ((K : ℝ))⁻¹) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      exact squeeze_zero (fun _ => norm_nonneg _) hbound htend_inv
  have htsum_tendsto : Tendsto (fun K : ℕ => ∑' j : ℕ, (onLineWeight e j : ℂ) * avg K j) atTop
      (𝓝 (∑' j : ℕ, if z j = 1 then (onLineWeight e j : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (summable_onLineWeight e) (fun j => ?_) (fun K j => ?_)
    · have h1 := tendsto_const_nhds (x := (onLineWeight e j : ℂ)).mul (havg_tendsto j)
      have heq : (onLineWeight e j : ℂ) * (if z j = 1 then (1 : ℂ) else 0) =
          if z j = 1 then (onLineWeight e j : ℂ) else 0 := by split_ifs <;> simp
      rwa [heq] at h1
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nonneg j)]
      exact mul_le_of_le_one_right (hw_nonneg j) (havg_norm K j)
  have hterm_summable : ∀ k : ℕ, Summable (fun j : ℕ => (onLineWeight e j : ℂ) * z j ^ k) := by
    intro k
    refine Summable.of_norm_bounded (summable_onLineWeight e) fun j => ?_
    rw [norm_mul, _root_.norm_pow, hz_norm j, one_pow, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (hw_nonneg j)]
  have hterm_tsum : ∀ k : ℕ, (∑' j : ℕ, (onLineWeight e j : ℂ) * z j ^ k) =
      (-1 : ℂ) ^ k * splineCorr ((k : ℝ) * Real.pi / γ₀) := by
    intro k
    rw [hspline_eq_bohr, ← tsum_mul_left]
    unfold bohrReal
    refine tsum_congr fun j => ?_
    have hpow : z j ^ k = (-1 : ℂ) ^ k *
        Complex.exp (Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (((k : ℝ) * Real.pi / γ₀ : ℝ) : ℂ)) := by
      have hz_eq : z j = (-1 : ℂ) *
          Complex.exp (Complex.I * (((e j : ℂ).im : ℝ) : ℂ) * (τ : ℂ)) := by
        simp [z]
      rw [hz_eq, mul_pow, ← Complex.exp_nat_mul]
      congr 2
      simp only [τ]
      push_cast
      ring
    rw [hpow]
    ring
  have hsum_interchange : ∀ K : ℕ,
      (∑' j : ℕ, ∑ k ∈ Finset.range K, (onLineWeight e j : ℂ) * z j ^ k) =
        ∑ k ∈ Finset.range K, (-1 : ℂ) ^ k * splineCorr ((k : ℝ) * Real.pi / γ₀) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        have hsumK : Summable (fun j : ℕ => ∑ k ∈ Finset.range K, (onLineWeight e j : ℂ) * z j ^ k) :=
          summable_sum fun k _ => hterm_summable k
        have hcongr : (fun j : ℕ => ∑ k ∈ Finset.range (K + 1), (onLineWeight e j : ℂ) * z j ^ k) =
            fun j : ℕ => (∑ k ∈ Finset.range K, (onLineWeight e j : ℂ) * z j ^ k) +
              (onLineWeight e j : ℂ) * z j ^ K := by
          ext j; exact Finset.sum_range_succ _ K
        rw [hcongr, hsumK.tsum_add (hterm_summable K), ih, hterm_tsum K, Finset.sum_range_succ]
  have hK_eq : ∀ K : ℕ,
      (∑' j : ℕ, (onLineWeight e j : ℂ) * avg K j) =
        (∑ k ∈ Finset.range K, (-1 : ℂ) ^ k * splineCorr ((k : ℝ) * Real.pi / γ₀)) / (K : ℂ) := by
    intro K
    have hcongr : (fun j : ℕ => (onLineWeight e j : ℂ) * avg K j) =
        fun j : ℕ => (∑ k ∈ Finset.range K, (onLineWeight e j : ℂ) * z j ^ k) * ((K : ℂ))⁻¹ := by
      ext j
      simp only [avg, div_eq_mul_inv, Finset.mul_sum, mul_assoc]
    rw [hcongr, tsum_mul_right, hsum_interchange K, div_eq_mul_inv]
  simp_rw [hK_eq] at htsum_tendsto
  have hre_bohr_tendsto : Tendsto (fun K : ℕ =>
      ((∑ k ∈ Finset.range K, (-1 : ℂ) ^ k * splineCorr ((k : ℝ) * Real.pi / γ₀)) / (K : ℂ)).re)
      atTop (𝓝 ((∑' j : ℕ, if z j = 1 then (onLineWeight e j : ℂ) else 0).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp htsum_tendsto
  have hre_borchers_tendsto : Tendsto (fun K : ℕ =>
      ((∑ k ∈ Finset.range K,
        (-1 : ℂ) ^ k * inner ℂ ψ₀ (B.U ((k : ℝ) * Real.pi / γ₀) ψ₀)) / (K : ℂ)).re)
      atTop (𝓝 0) := by
    simpa using Complex.continuous_re.continuousAt.tendsto.comp
      (B.alternating_cesaro_tendsto_zero hγ₀ ψ₀)
  have hre_K_eq : ∀ K : ℕ,
      ((∑ k ∈ Finset.range K, (-1 : ℂ) ^ k * splineCorr ((k : ℝ) * Real.pi / γ₀)) / (K : ℂ)).re =
        ((∑ k ∈ Finset.range K,
          (-1 : ℂ) ^ k * inner ℂ ψ₀ (B.U ((k : ℝ) * Real.pi / γ₀) ψ₀)) / (K : ℂ)).re := by
    intro K
    rcases eq_or_ne K 0 with rfl | _
    · simp
    · have hdiv_re : ∀ w : ℂ, (w / (K : ℂ)).re = w.re / (K : ℝ) := fun w => by
        rw [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, mul_comm,
          Complex.re_ofReal_mul, div_eq_mul_inv, mul_comm]
      rw [hdiv_re, hdiv_re]
      congr 1
      rw [Complex.re_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hpow_cast : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
      rw [hpow_cast, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        ← hc_eq_spline ((k : ℝ) * Real.pi / γ₀)]
  simp_rw [hre_K_eq] at hre_bohr_tendsto
  have hlim_zero : (∑' j : ℕ, if z j = 1 then (onLineWeight e j : ℂ) else 0).re = 0 :=
    tendsto_nhds_unique hre_bohr_tendsto hre_borchers_tendsto
  set wLim : ℕ → ℝ := fun j => if z j = 1 then onLineWeight e j else 0
  have hwLim_nonneg : ∀ j : ℕ, 0 ≤ wLim j := fun j => by
    dsimp only [wLim]; split_ifs; · exact hw_nonneg j; · exact le_rfl
  have hwLim_sum : Summable wLim :=
    (summable_onLineWeight e).of_nonneg_of_le hwLim_nonneg fun j => by
      dsimp only [wLim]; split_ifs; · exact le_rfl; · exact hw_nonneg j
  have htsum_re : (∑' j : ℕ, if z j = 1 then (onLineWeight e j : ℂ) else 0).re = ∑' j : ℕ, wLim j := by
    have hcast : (fun j : ℕ => if z j = 1 then (onLineWeight e j : ℂ) else 0) =
        fun j : ℕ => (wLim j : ℂ) := by
      ext j; dsimp only [wLim]; split_ifs <;> simp
    rw [hcast, ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [htsum_re] at hlim_zero
  have hge : onLineWeight e j₀ ≤ ∑' j : ℕ, wLim j := by
    have h1 := hwLim_sum.sum_le_tsum ({j₀} : Finset ℕ) (fun j _ => hwLim_nonneg j)
    simpa [wLim, hz_j₀] using h1
  linarith

/-- Exact one-sided GNS Born-rule corollary of `no_borchers_gns_tateLimit_integerProbe`. -/
theorem no_borchers_gns_bornRule_integerProbe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : BorchersPair H) (ψ₀ : H)
    (hborn : ∀ (N : ℕ) (a : Fin N → ℤ),
      ‖∑ i : Fin N, (a i : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀‖ ^ 2 = integerProbe N a) :
    False := by
  refine no_borchers_gns_tateLimit_integerProbe B ψ₀ fun N a => ?_
  have hev : (fun m : ℕ =>
      ‖∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • B.U (Real.log ((i : ℝ) + 1)) ψ₀‖ ^ 2 / (m : ℝ) ^ 2)
      =ᶠ[atTop] fun _ : ℕ => integerProbe N a := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ^ 2 ≠ 0 := by positivity
    rw [hborn N (m • a), integerProbe_smul, mul_div_cancel_left₀ _ hm0]
  exact tendsto_const_nhds.congr' hev.symm

/-- A Borchers–Wiesbrock half-sided modular inclusion carrying the partner involution: a
standard-form von Neumann algebra `(H, M, ms)` equipped with a `BorchersPair H` whose modular flow
`Δ` fixes `ms.Ω`, whose translation group `U` is inverted by modular conjugation
(`ms.J.conjOp (U a) = U (-a)`), and whose nonnegative shifts compress `M` into itself
(`U(a) M U(-a) ⊆ M` for `a ≥ 0`). -/
structure HalfSidedPartnerInclusion (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) where
  ms : StandardForm M
  B : BorchersPair H
  Δ_omega : ∀ s : ℝ, B.Δ s ms.Ω = ms.Ω
  J_U : ∀ a : ℝ, ms.J.conjOp (B.U a) = B.U (-a)
  half_sided : ∀ {a : ℝ}, 0 ≤ a → ∀ {A : H →L[ℂ] H}, A ∈ M → covShift B.U a A ∈ M

/-- **No half-sided modular inclusion carries the Hecke clock of `ζ` over `ℤ`.** In any
`HalfSidedPartnerInclusion`, every seed observable `A₀ ∈ M` generates covariant integer probes
`X(a) = ∑_{i < N} a_i U(log(i + 1)) A₀ U(-log(i + 1)) ∈ M`, and neither the cross-horizon
natural-cone quadratic form `Re ⟪Ω, X(a) (J X(a) J) Ω⟫` nor the one-sided GNS norm `‖X(a) Ω‖²` can
have Tate limit `integerProbe`. -/
theorem no_halfSided_modular_inclusion_carries_integerProbe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (hs : HalfSidedPartnerInclusion H M)
    {A₀ : H →L[ℂ] H} (hA₀ : A₀ ∈ M) :
    (∀ (N : ℕ) (a : Fin N → ℤ),
      (∑ i : Fin N, (a i : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀) ∈ M) ∧
    (¬ ∀ (N : ℕ) (a : Fin N → ℤ),
      Tendsto (fun m : ℕ =>
        (let X : H →L[ℂ] H :=
           ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀
         (inner ℂ hs.ms.Ω (X (hs.ms.J.conjOp X hs.ms.Ω))).re) / (m : ℝ) ^ 2)
        atTop (𝓝 (integerProbe N a))) ∧
    (¬ ∀ (N : ℕ) (a : Fin N → ℤ),
      Tendsto (fun m : ℕ =>
        (let X : H →L[ℂ] H :=
           ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀
         ‖X hs.ms.Ω‖ ^ 2) / (m : ℝ) ^ 2)
        atTop (𝓝 (integerProbe N a))) := by
  have hUΩ : ∀ a : ℝ, hs.B.U a hs.ms.Ω = hs.ms.Ω := hs.B.fix_of_delta_fix hs.Δ_omega
  refine ⟨fun N a => sum_mem fun i _ => M.smul_mem _
    (hs.half_sided (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i])) hA₀), ?_, ?_⟩
  · intro htate
    let U_pnat : ℕ+ → H →L[ℂ] H := fun n => hs.B.U (Real.log (n : ℝ))
    have hmul : ∀ m n : ℕ+, U_pnat (m * n) = U_pnat m * U_pnat n := fun m n => by
      dsimp only [U_pnat]
      have hcast : ((m * n : ℕ+) : ℝ) = (m : ℝ) * (n : ℝ) := by push_cast; rfl
      rw [hcast, Real.log_mul (by positivity) (by positivity), hs.B.U_add]
    have hiso : ∀ n : ℕ+, star (U_pnat n) * U_pnat n = 1 := fun n => hs.B.U_iso _
    have hΩ : ∀ n : ℕ+, U_pnat n hs.ms.Ω = hs.ms.Ω := fun n => hUΩ _
    have hJ : ∀ n : ℕ+, hs.ms.J.conjOp (U_pnat n) = star (U_pnat n) := fun n => by
      dsimp only [U_pnat]
      rw [hs.J_U, hs.B.star_U]
    refine no_vacuumFixing_partner_tateLimit_integerProbe hs.ms hmul hiso hΩ hJ A₀ fun N a => ?_
    have hX_eq : ∀ b : Fin N → ℤ,
        (∑ i : Fin N, (b i : ℂ) • covShift U_pnat (natPNat i) A₀) =
          ∑ i : Fin N, (b i : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀ := fun b => by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [U_pnat]
    simpa only [hX_eq] using htate N a
  · intro htate
    refine no_borchers_gns_tateLimit_integerProbe hs.B (A₀ hs.ms.Ω) fun N a => ?_
    have hact : ∀ b : Fin N → ℤ,
        (∑ i : Fin N, (b i : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀) hs.ms.Ω =
          ∑ i : Fin N, (b i : ℂ) • hs.B.U (Real.log ((i : ℝ) + 1)) (A₀ hs.ms.Ω) := fun b => by
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smul_apply, covShift_apply, hs.B.star_U, hUΩ]
    simpa only [hact] using htate N a

/-- **Partner Standard-Form Trichotomy over `ℤ`.** Across all Tomita–Takesaki standard-form
architectures `(H, M, ms)` implementing the partner involution via modular conjugation `J`:
1. *Internal partner unitaries* (`U(r) ∈ M`, `J U(r) J = U(r⁻¹)`) collapse into the center `M ∩ M'`
   and realize `integerProbe` via the natural-cone form if and only if `RiemannHypothesis` holds;
2. *External vacuum-fixing partner unitaries* (`U(n) Ω = Ω`, `J U(n) J = U(n)*`) unconditionally
   fail to realize `integerProbe` via the cross-horizon natural-cone Tate limit;
3. *External Borchers half-sided modular inclusions* unconditionally fail to realize `integerProbe`
   via either the cross-horizon natural-cone Tate limit or the one-sided GNS norm Tate limit. -/
theorem partner_standardForm_trichotomy :
    ((∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        {M : VonNeumannAlgebra H} (ms : StandardForm M) {U : posUnits → H →L[ℂ] H},
        U 1 = 1 → (∀ r s, U (r * s) = U r * U s) → (∀ r, U r ∈ M) →
        (∀ r, ms.J.conjOp (U r) = U r⁻¹) → ∀ r, U r ∈ M.commutant ∧ U r⁻¹ = star (U r)) ∧
      (RiemannHypothesis ↔
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
          (M : VonNeumannAlgebra H) (ms : StandardForm M) (U : posUnits → H →L[ℂ] H),
          U 1 = 1 ∧ (∀ r s, U (r * s) = U r * U s) ∧ (∀ r, U r ∈ M) ∧
          (∀ r, ms.J.conjOp (U r) = U r⁻¹) ∧
          ∀ (N : ℕ) (a : Fin N → ℤ),
            let X : H →L[ℂ] H := ∑ i : Fin N, (a i : ℂ) • U (natPosUnit i)
            (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re = integerProbe N a)) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        {M : VonNeumannAlgebra H} (ms : StandardForm M) {U : ℕ+ → H →L[ℂ] H},
        (∀ m n : ℕ+, U (m * n) = U m * U n) → (∀ n : ℕ+, star (U n) * U n = 1) →
        (∀ n : ℕ+, U n ms.Ω = ms.Ω) → (∀ n : ℕ+, ms.J.conjOp (U n) = star (U n)) →
        ∀ (A₀ : H →L[ℂ] H),
        ¬ ∀ (N : ℕ) (a : Fin N → ℤ),
          Tendsto (fun m : ℕ =>
            (let X : H →L[ℂ] H := ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift U (natPNat i) A₀
             (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re) / (m : ℝ) ^ 2)
            atTop (𝓝 (integerProbe N a))) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        {M : VonNeumannAlgebra H} (hs : HalfSidedPartnerInclusion H M) {A₀ : H →L[ℂ] H},
        A₀ ∈ M →
        (¬ ∀ (N : ℕ) (a : Fin N → ℤ),
          Tendsto (fun m : ℕ =>
            (let X : H →L[ℂ] H :=
               ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀
             (inner ℂ hs.ms.Ω (X (hs.ms.J.conjOp X hs.ms.Ω))).re) / (m : ℝ) ^ 2)
            atTop (𝓝 (integerProbe N a))) ∧
        (¬ ∀ (N : ℕ) (a : Fin N → ℤ),
          Tendsto (fun m : ℕ =>
            (let X : H →L[ℂ] H :=
               ∑ i : Fin N, (((m • a) i : ℤ) : ℂ) • covShift hs.B.U (Real.log ((i : ℝ) + 1)) A₀
             ‖X hs.ms.Ω‖ ^ 2) / (m : ℝ) ^ 2)
            atTop (𝓝 (integerProbe N a)))) :=
  ⟨⟨fun ms h1 hmul hM hJ r =>
      let ⟨hc, hs, _, _⟩ := standardForm_partner_rep_is_central_unitary ms h1 hmul hM hJ r
      ⟨hc, hs⟩,
    riemannHypothesis_iff_exists_standardForm_bornRule⟩,
   fun ms hmul hiso hΩ hJ A₀ htate =>
     no_vacuumFixing_partner_tateLimit_integerProbe ms hmul hiso hΩ hJ A₀ htate,
   fun hs hA₀ => (no_halfSided_modular_inclusion_carries_integerProbe hs hA₀).2⟩

#print axioms posGen_eq_zero_of_comm_antiunitaryInvol
#print axioms StandardForm.naturalCone_partner_hankel
#print axioms isMulHankel_and_heckeInv_iff_sqClass
#print axioms mulHankel_heckeInv_iff_factorsThrough_sqFreeCore
#print axioms exists_nontrivial_vacuumFixing_partner_standardForm_heckeInv
#print axioms const_of_mulHankel_eq_logToeplitz
#print axioms const_of_sqClass_laplaceMeasure
#print axioms BorchersPair.no_nontrivial_borchers_on_quadraticAlgebra
#print axioms BorchersPair.alternating_cesaro_tendsto_zero
#print axioms no_vacuumFixing_partner_tateLimit_integerProbe
#print axioms no_borchers_gns_tateLimit_integerProbe
#print axioms no_halfSided_modular_inclusion_carries_integerProbe
#print axioms partner_standardForm_trichotomy

end GaloisForLFunctions.CountingHolography

