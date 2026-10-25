import GaloisForLFunctions.ArithmeticPositiveDuality.HerglotzBochnerOnLattices
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface

/-!
# The two-prime spline orbit is a Bochner problem on the torus

Let `B` be the cubic spline and `C(u) = W(B(· − u), B)` its orbit correlation under Weil's form,
computed from primes, Gamma factor and pole. For two distinct primes the shifts
`⟨m, γ⟩ = m₁ log p + m₂ log q`, `m ∈ ℤ²`, form a copy of `ℤ²` in `ℝ`, and
`c_{p,q}(m) = C(−⟨m, γ⟩)` is a function on `ℤ²` (`twoPrimeCorr`).

* The Weil Gram matrix of translates is Toeplitz: `W(B(· − s), B(· − t)) = C(s − t)`
  (`weilGram_translate_cubicSpline`).
* **RH ⇔ rank-two positive definiteness** (`riemannHypothesis_iff_isPosDefOnLattice_twoPrimeCorr`).
  Under RH every Weil Gram matrix of real tests is positive semidefinite (the Pontryagin bound with
  no right zeros), so `c_{p,q}` is positive definite on `ℤ²`; conversely positive definiteness on
  `ℤ²` makes every Gram matrix on the two-prime orbit positive semidefinite, which is RH by the
  two-prime spline criterion.
* **RH ⇔ a positive measure on `T²`** (`riemannHypothesis_iff_exists_torusMeasure`). By
  Herglotz–Bochner on `ℤ²`, RH holds iff `c_{p,q}` is the coefficient sequence of a finite positive
  measure on the two-torus.

This is a receiver, an equivalent of RH, not a producer: it fixes the object that a rank-two
forcing law would have to construct. Rank one (a single tower `ℤ log p`) does not suffice
(`exists_symmetric_wolff_toeplitz_blind_configuration`); rank two does.
-/

open Complex Matrix MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open Zeta23 GaloisForLFunctions.HTGeometry
open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

/-- The von Mangoldt weight of Weil's form. -/
abbrev vonMangoldtWeight : ℕ → ℝ := fun k => (ArithmeticFunction.vonMangoldt k : ℝ)

/-- The orbit correlation of the cubic spline, `C(u) = W(B(· − u), B)`. -/
def splineCorr (u : ℝ) : ℂ :=
  RHTower.weilFullFunctional vonMangoldtWeight
    (EF.weilTest (ArithmeticCastelnuovoSeveri.translate u (cx cubicSpline)) (cx cubicSpline))

/-- The two-prime frequencies `(log p, log q)`. -/
def twoPrimeFreq (p q : ℕ) : Fin 2 → ℝ := ![Real.log p, Real.log q]

/-- The two-prime correlation on `ℤ²`: `c(m) = C(−(m₁ log p + m₂ log q))`. -/
def twoPrimeCorr (p q : ℕ) (m : Fin 2 → ℤ) : ℂ := splineCorr (-pairing m (twoPrimeFreq p q))

theorem weilTest_translate_translate (s t : ℝ) (f : ℝ → ℝ) :
    EF.weilTest (ArithmeticCastelnuovoSeveri.translate s (cx f))
        (ArithmeticCastelnuovoSeveri.translate t (cx f)) =
      EF.weilTest (ArithmeticCastelnuovoSeveri.translate (s - t) (cx f)) (cx f) :=
  weilTest_scaleShift_sub s t f f

/-- **The Weil Gram matrix of spline translates is Toeplitz.** -/
theorem weilGram_translate_cubicSpline {κ : Type*} (s : κ → ℝ) (a b : κ) :
    weilGram vonMangoldtWeight (fun a => ArithmeticCastelnuovoSeveri.translate (s a)
      (cx cubicSpline)) a b = splineCorr (s a - s b) := by
  unfold weilGram splineCorr
  rw [weilTest_translate_translate]

theorem pairing_sub' {ι : Type*} [Fintype ι] (m n : ι → ℤ) (θ : ι → ℝ) :
    pairing (m - n) θ = pairing m θ - pairing n θ := by
  rw [sub_eq_add_neg, pairing_add, pairing_neg, ← sub_eq_add_neg]

/-- The Gram form of the Toeplitz matrix is the Gram form of `c_{p,q}`. -/
theorem dotProduct_weilGram_eq {κ : Type*} [Fintype κ] (p q : ℕ) (x : κ → Fin 2 → ℤ)
    (c : κ → ℂ) :
    star c ⬝ᵥ (weilGram vonMangoldtWeight (fun a => ArithmeticCastelnuovoSeveri.translate
      (pairing (x a) (twoPrimeFreq p q)) (cx cubicSpline)) *ᵥ c) =
      ∑ a, ∑ b, star (c a) * twoPrimeCorr p q (x b - x a) * c b := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [weilGram_translate_cubicSpline, twoPrimeCorr, pairing_sub', neg_sub]
  ring

/-- A Hermitian matrix has no negative square iff it is positive semidefinite. -/
theorem hermNegIndex_eq_zero_iff_posSemidef' {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) : hermNegIndex H = 0 ↔ H.PosSemidef := by
  rw [negIndex_eq_card_neg_eigenvalues hH]
  constructor
  · intro hzero
    rw [hH.posSemidef_iff_eigenvalues_nonneg]
    intro i
    by_contra hi
    have himem : i ∈ ({j | hH.eigenvalues j < 0} : Finset n) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_not_ge hi
    rw [Finset.card_eq_zero.mp hzero] at himem
    simp at himem
  · intro hpsd
    apply Finset.card_eq_zero.mpr
    ext i
    simp [not_lt_of_ge (hpsd.eigenvalues_nonneg i)]

/-- Every two-prime shift is `⟨m, γ⟩` for some `m ∈ ℤ²`. -/
theorem exists_pairing_eq_of_mem_twoPrimeShifts {p q : ℕ} {s : ℝ}
    (hs : s ∈ twoPrimeShifts p q) : ∃ m : Fin 2 → ℤ, pairing m (twoPrimeFreq p q) = s := by
  unfold twoPrimeShifts at hs
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨![1, 0], by simp [pairing, twoPrimeFreq, Fin.sum_univ_two]⟩
    · exact ⟨![0, 1], by simp [pairing, twoPrimeFreq, Fin.sum_univ_two]⟩
  | zero => exact ⟨0, by simp [pairing]⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact ⟨m + n, pairing_add m n _⟩
  | neg x _ hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨-m, pairing_neg m _⟩

/-- **Under RH, the two-prime correlation is positive definite on `ℤ²`.** -/
theorem isPosDefOnLattice_twoPrimeCorr_of_rh (hRH : RiemannHypothesis) (p q : ℕ) :
    IsPosDefOnLattice (twoPrimeCorr p q) := by
  intro N x c
  set f : Fin N → ℝ → ℂ := fun a => ArithmeticCastelnuovoSeveri.translate
    (pairing (x a) (twoPrimeFreq p q)) (cx cubicSpline)
  have hneg : hermNegIndex (weilGram vonMangoldtWeight f) = 0 := by
    have h := negIndex_weilGram_le_offLineCount f
      (fun a => translate_contDiff (cx_contDiff contDiff_cubicSpline) _)
      (fun a => translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _)
    rw [riemannHypothesis_iff_no_rightZero.mp hRH, Set.encard_empty] at h
    exact_mod_cast nonpos_iff_eq_zero.mp h
  have hpsd := (hermNegIndex_eq_zero_iff_posSemidef' (weilGram_isHermitian _ f)).mp hneg
  have hq := (posSemidef_iff_dotProduct_mulVec.mp hpsd).2 c
  rw [dotProduct_weilGram_eq] at hq
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hq
  exact ⟨_, hre, Complex.ext rfl (by simpa using him.symm)⟩

/-- **Rank-two positive definiteness gives RH.** -/
theorem rh_of_isPosDefOnLattice_twoPrimeCorr {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hφ : IsPosDefOnLattice (twoPrimeCorr p q)) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero hp hq hpq]
  intro S hS
  have hx : ∀ s : S, ∃ m : Fin 2 → ℤ, pairing m (twoPrimeFreq p q) = s :=
    fun s => exists_pairing_eq_of_mem_twoPrimeShifts (hS s.2)
  choose x hx using hx
  have hfam : (fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline)) =
      fun s => ArithmeticCastelnuovoSeveri.translate (pairing (x s) (twoPrimeFreq p q))
        (cx cubicSpline) := funext fun s => by rw [hx s]
  rw [hfam, hermNegIndex_eq_zero_iff_posSemidef' (weilGram_isHermitian _ _),
    posSemidef_iff_dotProduct_mulVec]
  refine ⟨weilGram_isHermitian _ _, fun v => ?_⟩
  obtain ⟨r, hr, hsum⟩ := hφ.form x v
  rw [dotProduct_weilGram_eq, hsum]
  exact_mod_cast hr

/-- **RH is rank-two positive definiteness of the spline correlation.** -/
theorem riemannHypothesis_iff_isPosDefOnLattice_twoPrimeCorr {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ IsPosDefOnLattice (twoPrimeCorr p q) :=
  ⟨fun h => isPosDefOnLattice_twoPrimeCorr_of_rh h p q,
    rh_of_isPosDefOnLattice_twoPrimeCorr hp hq hpq⟩

/-- **RH is a Bochner problem on the two-torus.** RH holds iff the two-prime spline correlation
is the Fourier coefficient sequence of a finite positive measure on `T²`. -/
theorem riemannHypothesis_iff_exists_torusMeasure {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∃ μ : Measure (Fin 2 → ℝ), IsFiniteMeasure μ ∧
      ∀ m, fourierCoeff μ m = twoPrimeCorr p q m := by
  rw [riemannHypothesis_iff_isPosDefOnLattice_twoPrimeCorr hp hq hpq, isPosDefOnLattice_iff]

end GaloisForLFunctions.ArithmeticPositiveDuality
