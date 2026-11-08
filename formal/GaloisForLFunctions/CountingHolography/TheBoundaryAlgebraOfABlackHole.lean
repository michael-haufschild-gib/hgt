import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

/-!
# The boundary algebra of a black hole

The tool asked for in §2.10: **a boundary operator algebra whose GNS form on sources is Krein.** A black
hole of trace `t` and size `q` has the probe algebra `A = R[π]/(π² − tπ + q)`, Mathlib's
`QuadraticAlgebra R (−q) t`. Its natural involution is the **partner involution** `π* = t − π = q/π`,
which exchanges a mode with its functional-equation partner; it is Mathlib's conjugation.

* **The norm of a probe is its Krein square** (`norm_probe`): `N(y − xπ) = (y − xπ)(y − xπ)* =
  y² − t xy + q x²`. So for every normalized functional `ϕ` the GNS form `ϕ(a* a)` is the Krein square
  (`state_star_mul_self`): the GNS form on sources is Krein, whatever the state.
* **A positive state exists iff the black hole is damped** (`exists_positive_state_iff`), and iff the
  algebra has a `*`-representation on `ℂ` (`exists_starRep_iff`), the GNS representation sending `π` to the
  oscillating mode `t/2 + i√(q − t²/4)`. The count half of the count law is the positivity of the boundary
  algebra; the quadratic half is its existence.
* **A bank**: the product of the algebras of `g` oscillators has a faithful positive functional iff every
  oscillator is strictly damped (`exists_faithful_bank_iff`); its value on `a* a` is `Σ c_k 𝒬_k(a_k)`, the
  Born rules of `TheBornRulesOfAnOscillatorBank`.
* **Why `C*`-positivity is blind** (`trace_transpose_mul_self_nonneg`): with the Hilbert involution
  `A ↦ Aᵀ` the state `tr/2` is positive on every matrix, so the algebra of the delay is a `C*`-algebra on
  every black hole, fakes included. The count sees the partner involution, not the Hilbert one.
-/

open QuadraticAlgebra ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

/-! ### The probe algebra -/

section Probe

variable {R : Type*} [CommRing R] {q t : R}

/-- The probe `y − xπ` in the boundary algebra `R[π]/(π² − tπ + q)`. -/
def probe (q t : R) (x y : R) : QuadraticAlgebra R (-q) t := ⟨y, -x⟩

/-- `π` satisfies `π² = tπ − q`. -/
theorem omega_sq : (ω : QuadraticAlgebra R (-q) t) * ω = algebraMap R _ (-q) + t • ω := by
  ext <;> simp

/-- The partner involution sends `π` to `t − π`. -/
theorem star_omega : star (ω : QuadraticAlgebra R (-q) t) = algebraMap R _ t - ω := by
  ext <;> simp

/-- **The norm of an element is its Krein square**: `N(⟨y, w⟩) = 𝒬(−w, y)`. -/
theorem norm_eq_kreinSquare (z : QuadraticAlgebra R (-q) t) : z.norm = kreinSquare q t (-z.im) z.re := by
  rw [norm_def, kreinSquare]
  ring

/-- **The norm of a probe is its Krein square**: `N(y − xπ) = y² − t xy + q x²`. -/
theorem norm_probe (x y : R) : (probe q t x y).norm = kreinSquare q t x y := by
  rw [norm_eq_kreinSquare]
  simp [probe]

/-- `a* a` is the scalar `N(a)`. -/
theorem star_mul_self_eq (z : QuadraticAlgebra R (-q) t) : star z * z = algebraMap R _ z.norm := by
  rw [algebraMap_norm_eq_mul_star, mul_comm]

end Probe

/-! ### States and representations -/

section States

variable {q t : ℝ}

/-- **The GNS form on sources is Krein**: for every normalized functional `ϕ`, `ϕ(a* a) = N(a)`. -/
theorem state_star_mul_self (ϕ : QuadraticAlgebra ℝ (-q) t →ₗ[ℝ] ℝ) (hϕ : ϕ 1 = 1)
    (z : QuadraticAlgebra ℝ (-q) t) : ϕ (star z * z) = z.norm := by
  rw [star_mul_self_eq, Algebra.algebraMap_eq_smul_one, map_smul, hϕ, smul_eq_mul, mul_one]

/-- The norm `y² + t yw + q w²` is nonnegative iff `t² ≤ 4q`. -/
theorem norm_nonneg_iff : (∀ z : QuadraticAlgebra ℝ (-q) t, 0 ≤ z.norm) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have h1 := h ⟨-t / 2, 1⟩
    rw [norm_def] at h1
    simp only at h1
    nlinarith
  · intro ht z
    rw [norm_def]
    nlinarith [sq_nonneg (z.re + t * z.im / 2), sq_nonneg z.im,
      mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg z.im)]

/-- The real part, the state of the trivial probe. -/
def reState : QuadraticAlgebra ℝ (-q) t →ₗ[ℝ] ℝ where
  toFun z := z.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A positive state exists iff the black hole is damped.** -/
theorem exists_positive_state_iff :
    (∃ ϕ : QuadraticAlgebra ℝ (-q) t →ₗ[ℝ] ℝ, ϕ 1 = 1 ∧ ∀ z, 0 ≤ ϕ (star z * z)) ↔ t ^ 2 ≤ 4 * q := by
  rw [← norm_nonneg_iff]
  constructor
  · rintro ⟨ϕ, hϕ, hpos⟩ z
    rw [← state_star_mul_self ϕ hϕ]
    exact hpos z
  · intro h
    refine ⟨reState, rfl, fun z => ?_⟩
    rw [state_star_mul_self reState rfl]
    exact h z

/-- **The GNS representation exists iff the black hole is damped**: a `*`-homomorphism of the boundary
algebra to `ℂ` exists iff `t² ≤ 4q`; it sends `π` to the oscillating mode `t/2 + i√(q − t²/4)`. -/
theorem exists_starRep_iff :
    (∃ ρ : QuadraticAlgebra ℝ (-q) t →ₐ[ℝ] ℂ, ∀ z, ρ (star z) = conj (ρ z)) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · rintro ⟨ρ, hρ⟩
    rw [← norm_nonneg_iff]
    intro z
    -- `N(z) = ρ(z z*) = |ρ z|²`
    have h : ((z.norm : ℝ) : ℂ) = ρ z * conj (ρ z) := by
      rw [← hρ, ← map_mul, ← algebraMap_norm_eq_mul_star, AlgHom.commutes, Complex.coe_algebraMap]
    rw [Complex.mul_conj] at h
    have := Complex.ofReal_injective h
    rw [this]
    exact Complex.normSq_nonneg _
  · intro ht
    set s := Real.sqrt (q - t ^ 2 / 4)
    have hs : s ^ 2 = q - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
    set α : ℂ := ⟨t / 2, s⟩
    have hα : α * α = (-q) • (1 : ℂ) + t • α := by
      apply Complex.ext <;> simp [α, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]
    refine ⟨lift ⟨α, hα⟩, fun z => ?_⟩
    simp only [lift_apply_apply, re_star, im_star]
    apply Complex.ext
    · simp [α]
      ring
    · simp [α]

/-! ### Why `C*`-positivity is blind -/

/-- **The Hilbert involution is positive on every black hole**: `tr(Aᵀ A) ≥ 0` for every real `2 × 2`
matrix, the delay of a fake included. -/
theorem trace_transpose_mul_self_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ (A.transpose * A).trace := by
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 1 0), sq_nonneg (A 0 1), sq_nonneg (A 1 1)]

end States

/-! ### A bank of oscillators -/

section Bank

variable {ι : Type*} {q : ℝ} {t : ι → ℝ}

/-- The norm is positive definite iff `t² < 4q`. -/
theorem norm_pos_iff {t : ℝ} :
    (∀ z : QuadraticAlgebra ℝ (-q) t, z ≠ 0 → 0 < z.norm) ↔ t ^ 2 < 4 * q := by
  constructor
  · intro h
    have h1 := h ⟨-t / 2, 1⟩ (fun h0 => by
      have := congrArg QuadraticAlgebra.im h0
      simp at this)
    rw [norm_def] at h1
    simp only at h1
    nlinarith
  · intro ht z hz
    rw [norm_def]
    have hz' : z.re ≠ 0 ∨ z.im ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (QuadraticAlgebra.ext hc.1 hc.2)
    have hq : 0 < 4 * q - t ^ 2 := by linarith
    rcases hz' with h | h
    · rcases eq_or_ne z.im 0 with h0 | h0
      · rw [h0]
        have := sq_pos_of_ne_zero h
        nlinarith
      · nlinarith [sq_nonneg (z.re + t * z.im / 2), sq_pos_of_ne_zero h0, mul_pos hq (sq_pos_of_ne_zero h0)]
    · nlinarith [sq_nonneg (z.re + t * z.im / 2), sq_pos_of_ne_zero h, mul_pos hq (sq_pos_of_ne_zero h)]

/-- On the product algebra `a* a` is the family of norms. -/
theorem bank_star_mul_self (a : ∀ k, QuadraticAlgebra ℝ (-q) (t k)) :
    star a * a = fun k => algebraMap ℝ _ (a k).norm := by
  funext k
  rw [Pi.mul_apply, Pi.star_apply, star_mul_self_eq]

/-- **A bank has a faithful positive functional iff every oscillator is strictly damped.** The functional
`Σ_k Re` gives `ϕ(a* a) = Σ_k 𝒬_k(a_k)`, the equal-weight Born rule of the bank. -/
theorem exists_faithful_bank_iff [Fintype ι] [DecidableEq ι] :
    (∃ ϕ : (∀ k, QuadraticAlgebra ℝ (-q) (t k)) →ₗ[ℝ] ℝ, ∀ a, a ≠ 0 → 0 < ϕ (star a * a)) ↔
      ∀ k, t k ^ 2 < 4 * q := by
  constructor
  · rintro ⟨ϕ, hϕ⟩ k
    rw [← norm_pos_iff]
    -- `ω(a* a) = N(z) ω(e_k)` on `a = single k z`
    have hsingle : ∀ z : QuadraticAlgebra ℝ (-q) (t k),
        ϕ (star (Pi.single k z) * Pi.single k z) = z.norm * ϕ (Pi.single k 1) := by
      intro z
      have e : star (Pi.single k z) * Pi.single k z =
          z.norm • (Pi.single k 1 : ∀ k, QuadraticAlgebra ℝ (-q) (t k)) := by
        rw [bank_star_mul_self]
        funext j
        by_cases hj : j = k
        · subst hj
          simp [Algebra.algebraMap_eq_smul_one]
        · simp [hj]
      rw [e, map_smul, smul_eq_mul]
    have hk : 0 < ϕ (Pi.single k 1) := by
      have := hϕ (Pi.single k 1) (by
        intro h
        have := congrFun h k
        simp at this)
      rwa [hsingle, QuadraticAlgebra.norm_one, one_mul] at this
    intro z hz
    have := hϕ (Pi.single k z) (by
      intro h
      exact hz (by simpa using congrFun h k))
    rw [hsingle] at this
    exact pos_of_mul_pos_left this hk.le
  · intro ht
    refine ⟨∑ k, (reState (q := q) (t := t k)).comp (LinearMap.proj k), fun a ha => ?_⟩
    rw [bank_star_mul_self]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    have hre : ∀ k, reState (q := q) (t := t k) (algebraMap ℝ _ (a k).norm) = (a k).norm := fun k => by
      simp [reState]
    simp only [hre]
    obtain ⟨k₀, hk₀⟩ : ∃ k, a k ≠ 0 := by
      by_contra hc
      push Not at hc
      exact ha (funext hc)
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ (a k).norm := fun k _ =>
      (norm_nonneg_iff.mpr (ht k).le) (a k)
    exact lt_of_lt_of_le ((norm_pos_iff.mpr (ht k₀)) _ hk₀)
      (Finset.single_le_sum hnn (Finset.mem_univ k₀))

end Bank

end GaloisForLFunctions.CountingHolography

end

