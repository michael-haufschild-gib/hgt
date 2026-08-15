import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The divided-jet moment algebra of a signed density

A state with a root of multiplicity `m` at `r` is `F(u) = (u - r)^m G(u)` with `G` regular there,
and its divided jets `F/(u-r)^k` are the division-free expressions `(u - r)^(m-k) G(u)`.  All
pairings of divided jets against a density therefore reduce to the single family

`jetMoment η G r k = ∫ (u - r)^k · G u ^ 2 ∂η`,

with `k = 2m - p - q` for the pair `(F/(u-r)^p, F/(u-r)^q)`.  Multiplying one factor by the
coordinate — the parity transport from the even to the odd sector — is the exact one-step recursion

`∫ u (u - r)^k G² ∂η = jetMoment η G r (k+1) + r · jetMoment η G r k`,

so odd terminal energy is `r` times even terminal mass whenever the next moment vanishes.  Nothing
here is specific to a particular density: these are identities of the moment sequence.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {η : Measure ℝ}

/-- The `k`-th divided-jet moment of the regular part `G` at the root `r`. -/
def jetMoment (η : Measure ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, (u - r) ^ k * G u ^ 2 ∂η

/-- The cross moment of two regular parts at two roots. -/
def jetCrossMoment (η : Measure ℝ) (G H : ℝ → ℝ) (r s : ℝ) (k l : ℕ) : ℝ :=
  ∫ u : ℝ, (u - r) ^ k * G u * ((u - s) ^ l * H u) ∂η

theorem jetMoment_eq_jetCrossMoment (η : Measure ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ) :
    jetMoment η G r (2 * k) = jetCrossMoment η G G r r k k := by
  rw [jetMoment, jetCrossMoment]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (u - r) ^ (2 * k) * G u ^ 2 = (u - r) ^ k * G u * ((u - r) ^ k * G u)
  rw [two_mul, pow_add]
  ring

/-! ## The parity recursion -/

/-- **Multiplication by the coordinate is the one-step moment recursion.**  This is the exact
transport of an even divided-jet moment to its odd companion. -/
theorem integral_coord_mul_jet (η : Measure ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ)
    (h1 : Integrable (fun u : ℝ => (u - r) ^ (k + 1) * G u ^ 2) η)
    (h2 : Integrable (fun u : ℝ => (u - r) ^ k * G u ^ 2) η) :
    (∫ u : ℝ, u * ((u - r) ^ k * G u ^ 2) ∂η)
      = jetMoment η G r (k + 1) + r * jetMoment η G r k := by
  have hpt : ∀ u : ℝ, u * ((u - r) ^ k * G u ^ 2)
      = (u - r) ^ (k + 1) * G u ^ 2 + r * ((u - r) ^ k * G u ^ 2) := by
    intro u
    rw [pow_succ]
    ring
  rw [jetMoment, jetMoment, ← integral_const_mul]
  rw [← integral_add h1 (h2.const_mul r)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- **The terminal odd energy is the root times the terminal even mass.**  If the moment one step
above the terminal one vanishes, multiplying by the coordinate multiplies the terminal moment by
the root. -/
theorem integral_coord_mul_jet_terminal (η : Measure ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ)
    (h1 : Integrable (fun u : ℝ => (u - r) ^ (k + 1) * G u ^ 2) η)
    (h2 : Integrable (fun u : ℝ => (u - r) ^ k * G u ^ 2) η)
    (hvanish : jetMoment η G r (k + 1) = 0) :
    (∫ u : ℝ, u * ((u - r) ^ k * G u ^ 2) ∂η) = r * jetMoment η G r k := by
  rw [integral_coord_mul_jet η G r k h1 h2, hvanish, zero_add]

/-- The same recursion for a cross moment: multiplying the first factor by the coordinate raises
its jet index by one and adds `r` times the original. -/
theorem integral_coord_mul_jetCross (η : Measure ℝ) (G H : ℝ → ℝ) (r s : ℝ) (k l : ℕ)
    (h1 : Integrable (fun u : ℝ => (u - r) ^ (k + 1) * G u * ((u - s) ^ l * H u)) η)
    (h2 : Integrable (fun u : ℝ => (u - r) ^ k * G u * ((u - s) ^ l * H u)) η) :
    (∫ u : ℝ, u * ((u - r) ^ k * G u * ((u - s) ^ l * H u)) ∂η)
      = jetCrossMoment η G H r s (k + 1) l + r * jetCrossMoment η G H r s k l := by
  have hpt : ∀ u : ℝ, u * ((u - r) ^ k * G u * ((u - s) ^ l * H u))
      = (u - r) ^ (k + 1) * G u * ((u - s) ^ l * H u)
        + r * ((u - r) ^ k * G u * ((u - s) ^ l * H u)) := by
    intro u
    rw [pow_succ]
    ring
  rw [jetCrossMoment, jetCrossMoment, ← integral_const_mul]
  rw [← integral_add h1 (h2.const_mul r)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- A cross moment is the moment of the merged regular part against the merged root factor. -/
theorem jetCrossMoment_eq (η : Measure ℝ) (G H : ℝ → ℝ) (r s : ℝ) (k l : ℕ) :
    jetCrossMoment η G H r s k l
      = ∫ u : ℝ, (u - r) ^ k * (u - s) ^ l * (G u * H u) ∂η := by
  rw [jetCrossMoment]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

/-! ## Nonnegativity of the terminal mass -/

/-- An even divided-jet moment is nonnegative: its integrand is a square. -/
theorem jetMoment_even_nonneg (η : Measure ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ) :
    0 ≤ jetMoment η G r (2 * k) := by
  rw [jetMoment]
  refine integral_nonneg fun u => ?_
  have h : (u - r) ^ (2 * k) = ((u - r) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [h]
  positivity

end GaloisForLFunctions.HTGeometry

end
