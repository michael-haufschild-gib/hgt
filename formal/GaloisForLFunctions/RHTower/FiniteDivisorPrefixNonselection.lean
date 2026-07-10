/-
# Finite divisor-prefix orbit nonselection (no jets)

The exact finite divisor already verified on the critical line does not select the type of a later
reflection orbit.  Given arbitrary positive critical-line representatives and multiplicities, the
carrier `lineDivisorPrefix` realizes that divisor exactly.  After attaching any finite exact Euler
head, it admits both:

* a fixed-orbit extension by a new critical-line pair; and
* a free-orbit extension at an arbitrary generic off-line point of the open strip.

Both extensions retain every prescribed old multiplicity exactly, and the added orbit is simple.
The result uses values and divisors only—no derivatives, Taylor data, or jets.

This is a `[BRIDGE]`/no-go theorem, not a numerical amplification of the verified zeta bound: the
constructed carriers are members of the finite-Euler-decorated FE/Schwarz class, not the completed
zeta function.  Its consequence is structural: finite divisor data plus every finite Euler head is
insufficient; any positive amplifier must use a genuinely infinite source constraint that free-orbit
multiplication fails to preserve.
-/
import GaloisForLFunctions.RHTower.FiniteEulerInert

noncomputable section

namespace RHTower

open Complex

/-- The positive critical-line representative of the reflection orbit at ordinate `τ`. -/
def criticalLinePoint (τ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (τ : ℂ) * Complex.I

/-- The carrier of a finite critical-line divisor with prescribed multiplicities. -/
def lineDivisorPrefix (S : Finset ℝ) (m : ℝ → ℕ) : ℂ → ℂ :=
  fun s => ∏ τ ∈ S, (linePair τ s) ^ (m τ)

/-- A fixed-orbit extension of a finite critical-line divisor, with a finite Euler head. -/
def fixedOrbitExtension (P : Finset ℕ) (S : Finset ℝ) (m : ℝ → ℕ) (η : ℝ) : ℂ → ℂ :=
  fun s => feBundle P s * (lineDivisorPrefix S m s * linePair η s)

/-- A free-orbit extension of a finite critical-line divisor, with the same finite Euler head. -/
def freeOrbitExtension (P : Finset ℕ) (S : Finset ℝ) (m : ℝ → ℕ) (ρ : ℂ) : ℂ → ℂ :=
  fun s => feBundle P s * (lineDivisorPrefix S m s * orbitQuartic ρ s)

@[simp] theorem criticalLinePoint_re (τ : ℝ) : (criticalLinePoint τ).re = 1 / 2 := by
  simp [criticalLinePoint]

@[simp] theorem criticalLinePoint_im (τ : ℝ) : (criticalLinePoint τ).im = τ := by
  simp [criticalLinePoint]

/-- Evaluation of one crease block at another critical-line representative. -/
theorem linePair_criticalLinePoint (σ τ : ℝ) :
    linePair σ (criticalLinePoint τ) = ((σ ^ 2 - τ ^ 2 : ℝ) : ℂ) := by
  rw [linePair_eq]
  simp only [criticalLinePoint]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Distinct positive critical-line representatives do not collide. -/
theorem linePair_ne_zero_at_distinct_positive {σ τ : ℝ}
    (hσ : 0 < σ) (hτ : 0 < τ) (hne : σ ≠ τ) :
    linePair σ (criticalLinePoint τ) ≠ 0 := by
  rw [linePair_criticalLinePoint, Complex.ofReal_ne_zero]
  intro hsq
  have : σ = τ := by nlinarith
  exact hne this

/-- A crease block is nonzero at every off-critical-line point. -/
theorem linePair_ne_zero_at_offline (τ : ℝ) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) :
    linePair τ ρ ≠ 0 := by
  simp only [linePair, mul_ne_zero_iff, sub_ne_zero]
  constructor <;> intro h
  · apply hρ
    have hre := congrArg Complex.re h
    simpa using hre
  · apply hρ
    have hre := congrArg Complex.re h
    simpa using hre

/-- A free `V₄` orbit never meets the critical line. -/
theorem orbitQuartic_ne_zero_at_criticalLinePoint {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) (τ : ℝ) :
    orbitQuartic ρ (criticalLinePoint τ) ≠ 0 := by
  unfold orbitQuartic
  refine mul_ne_zero ?_ (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · intro h
    apply hρ
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, criticalLinePoint_re, Complex.zero_re] at hre
    linarith
  · intro h
    apply hρ
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, criticalLinePoint_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  · intro h
    apply hρ
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, criticalLinePoint_re, Complex.conj_re, Complex.zero_re] at hre
    linarith
  · intro h
    apply hρ
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, criticalLinePoint_re, Complex.one_re, Complex.conj_re,
      Complex.zero_re] at hre
    linarith

/-- The finite critical-line divisor carrier has FE and Schwarz symmetry. -/
theorem lineDivisorPrefix_fESchwarz (S : Finset ℝ) (m : ℝ → ℕ) :
    FESchwarz (lineDivisorPrefix S m) := by
  unfold lineDivisorPrefix
  exact FESchwarz.finsetProd S (fun τ s => (linePair τ s) ^ (m τ))
    (fun τ _ => (fESchwarz_linePair τ).pow (m τ))

/-- The finite critical-line carrier realizes every prescribed positive-height multiplicity exactly. -/
theorem lineDivisorPrefix_order (S : Finset ℝ) (m : ℝ → ℕ)
    (hS : ∀ τ ∈ S, 0 < τ) {τ : ℝ} (hτ : τ ∈ S) :
    analyticOrderAt (lineDivisorPrefix S m) (criticalLinePoint τ) = m τ := by
  unfold lineDivisorPrefix
  exact analyticOrderAt_prodPow_at S linePair m (criticalLinePoint τ) τ hτ
    (fun σ _ => (fESchwarz_linePair σ).1.analyticAt _)
    (linePair_order (ne_of_gt (hS τ hτ)))
    (fun σ hσ hστ => linePair_ne_zero_at_distinct_positive
      (hS σ hσ) (hS τ hτ) hστ)

/-- The finite critical-line carrier is nonzero at a fresh positive fixed orbit. -/
theorem lineDivisorPrefix_ne_zero_at_fresh (S : Finset ℝ) (m : ℝ → ℕ)
    (hS : ∀ τ ∈ S, 0 < τ) {η : ℝ} (hη : 0 < η) (hηS : η ∉ S) :
    lineDivisorPrefix S m (criticalLinePoint η) ≠ 0 := by
  unfold lineDivisorPrefix
  rw [Finset.prod_ne_zero_iff]
  intro τ hτ
  exact pow_ne_zero (m τ) (linePair_ne_zero_at_distinct_positive
    (hS τ hτ) hη (fun h => hηS (h ▸ hτ)))

/-- The finite critical-line carrier is nonzero at every off-critical-line point. -/
theorem lineDivisorPrefix_ne_zero_at_offline (S : Finset ℝ) (m : ℝ → ℕ) {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) : lineDivisorPrefix S m ρ ≠ 0 := by
  unfold lineDivisorPrefix
  rw [Finset.prod_ne_zero_iff]
  intro τ hτ
  exact pow_ne_zero (m τ) (linePair_ne_zero_at_offline τ hρ)

/-- Both orbit extensions lie in the same finite-Euler-decorated FE/Schwarz class. -/
theorem orbitExtensions_finiteEulerClass
    (P : Finset ℕ) (S : Finset ℝ) (m : ℝ → ℕ) (η : ℝ) (ρ : ℂ) :
    FiniteEulerClass P (fixedOrbitExtension P S m η) ∧
      FiniteEulerClass P (freeOrbitExtension P S m ρ) := by
  constructor
  · exact ⟨fun s => lineDivisorPrefix S m s * linePair η s,
      (lineDivisorPrefix_fESchwarz S m).mul (fESchwarz_linePair η), fun _ => rfl⟩
  · exact ⟨fun s => lineDivisorPrefix S m s * orbitQuartic ρ s,
      (lineDivisorPrefix_fESchwarz S m).mul (fESchwarz_orbitQuartic ρ), fun _ => rfl⟩

/-- **Finite divisor-prefix orbit nonselection.**  Every finite positive critical-line divisor,
decorated by any finite collection of exact Euler factors, has two FE/Schwarz extensions that agree
exactly on the entire prescribed divisor.  One extension adds a fresh simple fixed reflection orbit;
the other adds a simple free off-line orbit at an arbitrary generic point of the open strip. -/
theorem finiteDivisorPrefix_orbitNonselection
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p)
    (S : Finset ℝ) (m : ℝ → ℕ) (hS : ∀ τ ∈ S, 0 < τ)
    {η : ℝ} (hη : 0 < η) (hηS : η ∉ S)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hρre : ρ.re ≠ 1 / 2) (hρim : ρ.im ≠ 0) :
    FiniteEulerClass P (fixedOrbitExtension P S m η) ∧
      FiniteEulerClass P (freeOrbitExtension P S m ρ) ∧
      (∀ τ ∈ S,
        analyticOrderAt (fixedOrbitExtension P S m η) (criticalLinePoint τ) = m τ ∧
        analyticOrderAt (freeOrbitExtension P S m ρ) (criticalLinePoint τ) = m τ) ∧
      analyticOrderAt (fixedOrbitExtension P S m η) (criticalLinePoint η) = 1 ∧
      analyticOrderAt (freeOrbitExtension P S m ρ) ρ = 1 := by
  have hclasses := orbitExtensions_finiteEulerClass P S m η ρ
  refine ⟨hclasses.1, hclasses.2, ?_, ?_, ?_⟩
  · intro τ hτ
    have hτ0 : 0 < (criticalLinePoint τ).re := by norm_num
    have hτ1 : (criticalLinePoint τ).re < 1 := by norm_num
    constructor
    · change analyticOrderAt
        (fun s => feBundle P s * (lineDivisorPrefix S m * linePair η) s)
          (criticalLinePoint τ) = m τ
      rw [
        feBundle_divisor_inert P hP
          ((lineDivisorPrefix_fESchwarz S m).1.mul (fESchwarz_linePair η).1) hτ0 hτ1,
        analyticOrderAt_mul
          ((lineDivisorPrefix_fESchwarz S m).1.analyticAt _)
          ((fESchwarz_linePair η).1.analyticAt _),
        lineDivisorPrefix_order S m hS hτ,
        analyticOrderAt_eq_zero.mpr (Or.inr
          (linePair_ne_zero_at_distinct_positive hη (hS τ hτ)
            (fun h => hηS (h ▸ hτ)))), add_zero]
    · change analyticOrderAt
        (fun s => feBundle P s * (lineDivisorPrefix S m * orbitQuartic ρ) s)
          (criticalLinePoint τ) = m τ
      rw [
        feBundle_divisor_inert P hP
          ((lineDivisorPrefix_fESchwarz S m).1.mul (fESchwarz_orbitQuartic ρ).1) hτ0 hτ1,
        analyticOrderAt_mul
          ((lineDivisorPrefix_fESchwarz S m).1.analyticAt _)
          ((fESchwarz_orbitQuartic ρ).1.analyticAt _),
        lineDivisorPrefix_order S m hS hτ,
        analyticOrderAt_eq_zero.mpr (Or.inr
          (orbitQuartic_ne_zero_at_criticalLinePoint hρre τ)), add_zero]
  · have hη0 : 0 < (criticalLinePoint η).re := by norm_num
    have hη1 : (criticalLinePoint η).re < 1 := by norm_num
    change analyticOrderAt
      (fun s => feBundle P s * (lineDivisorPrefix S m * linePair η) s)
        (criticalLinePoint η) = 1
    rw [
      feBundle_divisor_inert P hP
        ((lineDivisorPrefix_fESchwarz S m).1.mul (fESchwarz_linePair η).1) hη0 hη1,
      analyticOrderAt_mul
        ((lineDivisorPrefix_fESchwarz S m).1.analyticAt _)
        ((fESchwarz_linePair η).1.analyticAt _),
      analyticOrderAt_eq_zero.mpr (Or.inr
        (lineDivisorPrefix_ne_zero_at_fresh S m hS hη hηS)),
      zero_add]
    simpa only [criticalLinePoint] using linePair_order (ne_of_gt hη)
  · change analyticOrderAt
      (fun s => feBundle P s * (lineDivisorPrefix S m * orbitQuartic ρ) s) ρ = 1
    rw [
      feBundle_divisor_inert P hP
        ((lineDivisorPrefix_fESchwarz S m).1.mul (fESchwarz_orbitQuartic ρ).1) hρ0 hρ1,
      analyticOrderAt_mul
        ((lineDivisorPrefix_fESchwarz S m).1.analyticAt _)
        ((fESchwarz_orbitQuartic ρ).1.analyticAt _),
      analyticOrderAt_eq_zero.mpr (Or.inr
        (lineDivisorPrefix_ne_zero_at_offline S m hρre)),
      orbitQuartic_order_one hρre hρim, zero_add]

end RHTower
