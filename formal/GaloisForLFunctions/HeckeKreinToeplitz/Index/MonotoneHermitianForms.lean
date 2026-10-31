import GaloisForLFunctions.HTGeometry.AppellHumbertGaussianBound
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Bounded monotone limits of Hermitian forms

Increasing bounded diagonal values determine a pointwise limit by polarization. Hermitian symmetry, linearity, and nonnegativity pass to this limit.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Complex polarization of a real quadratic function, with the first argument linear. -/
def hermitianPolarization (d : V → ℝ) (x y : V) : ℂ :=
  ((d (x + y) - d (x + (-1 : ℂ) • y) : ℝ) : ℂ) / 4 +
    I * ((d (x + I • y) - d (x + (-I) • y) : ℝ) : ℂ) / 4

/-- The four diagonal values recover a Hermitian form. -/
theorem hermitianPolarization_diag {H : V → V → ℂ} (hH : IsHermitianForm H)
    (x y : V) : hermitianPolarization (fun v => (H v v).re) x y = H x y := by
  simp only [hermitianPolarization, Complex.ofReal_sub, ← hH.self_eq_re]
  simp only [hH.add_left, hH.add_right, hH.smul_left, hH.smul_right,
    star_neg, star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The form determined by the suprema of an increasing family's diagonal values. -/
def monotoneHermitianLimit (H : ℕ → V → V → ℂ) : V → V → ℂ :=
  hermitianPolarization (fun v => ⨆ n, (H n v v).re)

/-- Bounded increasing Hermitian diagonals yield pointwise convergence by polarization. -/
theorem tendsto_monotoneHermitianLimit (H : ℕ → V → V → ℂ)
    (hH : ∀ n, IsHermitianForm (H n))
    (hmono : ∀ v, Monotone (fun n => (H n v v).re))
    (hbdd : ∀ v, BddAbove (Set.range (fun n => (H n v v).re))) (x y : V) :
    Tendsto (fun n => H n x y) atTop (𝓝 (monotoneHermitianLimit H x y)) := by
  have hD (v : V) : Tendsto (fun n => ((H n v v).re : ℂ)) atTop
      (𝓝 ((⨆ n, (H n v v).re : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_atTop_ciSup (hmono v) (hbdd v))
  have hlim := (((hD (x + y)).sub (hD (x + (-1 : ℂ) • y))).div_const (4 : ℂ)).add
    (((tendsto_const_nhds (x := (I : ℂ))).mul
      ((hD (x + I • y)).sub (hD (x + (-I) • y)))).div_const (4 : ℂ))
  have hpolar : Tendsto (fun n => hermitianPolarization (fun v => (H n v v).re) x y)
      atTop (𝓝 (monotoneHermitianLimit H x y)) := by
    simpa only [hermitianPolarization, monotoneHermitianLimit, Complex.ofReal_sub] using hlim
  exact hpolar.congr' (Eventually.of_forall fun n => hermitianPolarization_diag (hH n) x y)

/-- Pointwise limits preserve the Hermitian form laws. -/
theorem isHermitianForm_of_pointwise_tendsto {H : ℕ → V → V → ℂ}
    {A : V → V → ℂ} (hH : ∀ n, IsHermitianForm (H n))
    (hlim : ∀ x y, Tendsto (fun n => H n x y) atTop (𝓝 (A x y))) :
    IsHermitianForm A := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    have he : (fun n => H n (x + y) z) = (fun n => H n x z + H n y z) :=
      funext fun n => (hH n).add_left x y z
    have ht := (hlim x z).add (hlim y z)
    rw [← he] at ht
    exact tendsto_nhds_unique (hlim (x + y) z) ht
  · intro a x y
    have he : (fun n => H n (a • x) y) = (fun n => a * H n x y) :=
      funext fun n => (hH n).smul_left a x y
    have ht := (tendsto_const_nhds (x := a)).mul (hlim x y)
    rw [← he] at ht
    exact tendsto_nhds_unique (hlim (a • x) y) ht
  · intro x y
    have he : (fun n => H n y x) = (fun n => star (H n x y)) :=
      funext fun n => (hH n).symm x y
    have ht := (hlim x y).star
    rw [← he] at ht
    exact tendsto_nhds_unique (hlim y x) ht

/-- A bounded increasing family of nonnegative Hermitian forms has a nonnegative Hermitian limit. -/
theorem monotoneHermitianLimit_isHermitian_nonnegative (H : ℕ → V → V → ℂ)
    (hH : ∀ n, IsHermitianForm (H n)) (hpos : ∀ n v, 0 ≤ (H n v v).re)
    (hmono : ∀ v, Monotone (fun n => (H n v v).re))
    (hbdd : ∀ v, BddAbove (Set.range (fun n => (H n v v).re))) :
    IsHermitianForm (monotoneHermitianLimit H) ∧
      ∀ v, 0 ≤ (monotoneHermitianLimit H v v).re := by
  have hlim := tendsto_monotoneHermitianLimit H hH hmono hbdd
  refine ⟨isHermitianForm_of_pointwise_tendsto hH hlim, ?_⟩
  intro v
  exact ge_of_tendsto'
    (Complex.continuous_re.continuousAt.tendsto.comp (hlim v v)) (fun n => hpos n v)

#print axioms hermitianPolarization_diag
#print axioms monotoneHermitianLimit_isHermitian_nonnegative
end GaloisForLFunctions.HeckeKreinToeplitz
