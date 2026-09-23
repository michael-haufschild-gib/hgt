import GaloisForLFunctions.HTGeometry.FeatureKernelResolventBound

/-!
# The spectral resolvent of a feature kernel

Each spectral mode of a centred feature kernel contributes its own geometric series, so the
discounted resolvent kernel is the Neumann sum of the spectrally weighted kernels.  Contractive
spectral weights only shrink the diagonal, so the reproducing Cauchy--Schwarz gives every Neumann
summand the same leverage bound and the geometric series closes.  No `L^∞` contractivity of the
transition operator is needed: the weights are on the modes.

Under a transitive measure-preserving symmetry the diagonal is constant, hence equal to its own
average, which is the trace of the centred projection.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {iota X : Type*} [Fintype iota]

/-- The `m`-th spectral power of a feature kernel. -/
def spectralPowerKernel (phi : iota → X → ℝ) (lam : iota → ℝ) (m : ℕ) (x y : X) : ℝ :=
  ∑ j, lam j ^ m * (phi j x * phi j y)

@[simp] theorem spectralPowerKernel_zero (phi : iota → X → ℝ) (lam : iota → ℝ) (x y : X) :
    spectralPowerKernel phi lam 0 x y = featureKernel phi x y := by
  unfold spectralPowerKernel featureKernel
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Every spectral power of a feature kernel inherits the leverage bound.**  Contractive spectral
weights only shrink the diagonal, so the reproducing Cauchy--Schwarz still applies. -/
theorem abs_spectralPowerKernel_le {phi : iota → X → ℝ} {lam : iota → ℝ} {L : ℝ}
    (hlam : ∀ j, |lam j| ≤ 1) (hL : ∀ x, featureKernel phi x x ≤ L) (m : ℕ) (x y : X) :
    |spectralPowerKernel phi lam m x y| ≤ L := by
  have hL0 : 0 ≤ L := le_trans (featureKernel_diag_nonneg phi x) (hL x)
  have hweight : ∀ j, (lam j ^ m) ^ (2 : ℕ) ≤ 1 := by
    intro j
    have h1 : |lam j ^ m| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hlam j)
    nlinarith [abs_nonneg (lam j ^ m), sq_abs (lam j ^ m)]
  have hdiag : ∀ z : X, (∑ j, (lam j ^ m * phi j z) ^ (2 : ℕ)) ≤ L := by
    intro z
    calc
      (∑ j, (lam j ^ m * phi j z) ^ (2 : ℕ)) ≤ ∑ j, phi j z ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [mul_pow]
        nlinarith [sq_nonneg (phi j z), hweight j]
      _ = featureKernel phi z z := (Finset.sum_congr rfl fun j _ => by ring)
      _ ≤ L := hL z
  have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => lam j ^ m * phi j x) (fun j => phi j y)
  have heq : (∑ j, lam j ^ m * phi j x * phi j y) = spectralPowerKernel phi lam m x y := by
    unfold spectralPowerKernel
    exact Finset.sum_congr rfl fun j _ => by ring
  have hy : (∑ j, phi j y ^ (2 : ℕ)) ≤ L := by
    calc (∑ j, phi j y ^ (2 : ℕ)) = featureKernel phi y y :=
          (Finset.sum_congr rfl fun j _ => by ring)
      _ ≤ L := hL y
  rw [heq] at hcs
  have hsq : spectralPowerKernel phi lam m x y ^ (2 : ℕ) ≤ L * L := by
    refine le_trans hcs ?_
    refine mul_le_mul (hdiag x) hy ?_ hL0
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith [hsq, abs_nonneg (spectralPowerKernel phi lam m x y),
    sq_abs (spectralPowerKernel phi lam m x y), hL0]

/-- The centred discounted resolvent kernel `(4)`. -/
noncomputable def spectralResolventKernel (phi : iota → X → ℝ) (lam : iota → ℝ) (a : ℝ) (x y : X) : ℝ :=
  ∑ j, (phi j x * phi j y) / (1 - a * lam j)

/-- **The Neumann expansion of the resolvent kernel.**  Each spectral mode contributes its own
geometric series, and the finite sum over modes may be exchanged with it. -/
theorem spectralResolventKernel_eq_tsum {phi : iota → X → ℝ} {lam : iota → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hlam : ∀ j, |lam j| ≤ 1) (x y : X) :
    spectralResolventKernel phi lam a x y = ∑' m : ℕ, a ^ m * spectralPowerKernel phi lam m x y := by
  have hlt : ∀ j : iota, |a * lam j| < 1 := by
    intro j
    rw [abs_mul, abs_of_nonneg ha]
    calc a * |lam j| ≤ a * 1 := mul_le_mul_of_nonneg_left (hlam j) ha
      _ = a := mul_one a
      _ < 1 := ha1
  have hmode : ∀ j : iota, HasSum (fun m : ℕ => (a * lam j) ^ m * (phi j x * phi j y))
      ((phi j x * phi j y) / (1 - a * lam j)) := by
    intro j
    have hgeom : HasSum (fun m : ℕ => (a * lam j) ^ m) (1 - a * lam j)⁻¹ :=
      hasSum_geometric_of_abs_lt_one (hlt j)
    have := hgeom.mul_right (phi j x * phi j y)
    rwa [inv_mul_eq_div] at this
  have hall : HasSum (fun m : ℕ => ∑ j, (a * lam j) ^ m * (phi j x * phi j y))
      (∑ j, (phi j x * phi j y) / (1 - a * lam j)) :=
    hasSum_sum fun j _ => hmode j
  have hrw : (fun m : ℕ => ∑ j, (a * lam j) ^ m * (phi j x * phi j y)) =
      fun m : ℕ => a ^ m * spectralPowerKernel phi lam m x y := by
    funext m
    unfold spectralPowerKernel
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [hrw] at hall
  exact (hall.tsum_eq).symm

/-- **`(8b)`.**  The leverage bounds the centred discounted resolvent kernel. -/
theorem abs_spectralResolventKernel_le {phi : iota → X → ℝ} {lam : iota → ℝ} {a L : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hlam : ∀ j, |lam j| ≤ 1)
    (hL : ∀ x, featureKernel phi x x ≤ L) (x y : X) :
    |spectralResolventKernel phi lam a x y| ≤ L / (1 - a) := by
  rw [spectralResolventKernel_eq_tsum ha ha1 hlam]
  refine abs_tsum_le_of_geometric ha ha1 _ fun m => ?_
  rw [abs_mul, abs_pow, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (abs_spectralPowerKernel_le hlam hL m x y) (by positivity)

/-- **`(8c)`.**  Under a transitive symmetry the diagonal is constant, hence equal to the trace of
the centred projection: the number of centred modes. -/
theorem featureKernel_diag_eq_card_of_const {X : Type*} [Fintype X]
    (phi : iota → X → ℝ) (pi : X → ℝ) (hpi : ∑ x, pi x = 1)
    (hortho : ∀ j, ∑ x, pi x * phi j x ^ (2 : ℕ) = 1)
    {c : ℝ} (hconst : ∀ x, featureKernel phi x x = c) :
    c = (Fintype.card iota : ℝ) := by
  have h1 : ∑ x, pi x * featureKernel phi x x = c := by
    simp_rw [hconst]
    rw [← Finset.sum_mul, hpi, one_mul]
  have h2 : ∑ x, pi x * featureKernel phi x x = (Fintype.card iota : ℝ) := by
    have hexp : ∀ x : X, pi x * featureKernel phi x x = ∑ j, pi x * phi j x ^ (2 : ℕ) := by
      intro x
      unfold featureKernel
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ => hortho j]
    simp
  linarith

noncomputable section

section MatrixCoefficients

variable {X : Type*} {N : ℕ}

/-- The real observables of a complex matrix-coefficient sector: the constants together with the
real and imaginary parts of every matrix entry of the representation. -/
def matrixCoefficientFamily (rho : X → Matrix (Fin N) (Fin N) ℂ) :
    Option (Bool × (Fin N × Fin N)) → (X → ℝ)
  | none => fun _ => 1
  | some (false, p) => fun x => (rho x p.1 p.2).re
  | some (true, p) => fun x => (rho x p.1 p.2).im

/-- **`(8e)`, the dimension count.**  The real matrix-coefficient sector of a representation of
complex dimension `N` has dimension at most `2N² + 1`. -/
theorem finrank_matrixCoefficientSector_le (rho : X → Matrix (Fin N) (Fin N) ℂ) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range (matrixCoefficientFamily rho))) ≤ 2 * N ^ (2 : ℕ) + 1 := by
  refine le_trans (finrank_range_le_card (matrixCoefficientFamily rho)) ?_
  have hcard : Fintype.card (Option (Bool × (Fin N × Fin N))) = 2 * N ^ (2 : ℕ) + 1 := by
    simp [Fintype.card_option, Fintype.card_prod]
    ring
  rw [hcard]

end MatrixCoefficients

end

noncomputable section

section Transitive

variable {iota X : Type*} [Fintype iota] [DecidableEq iota]

/-- A symmetry of the state space acts on the feature family by an orthogonal coefficient
matrix. -/
def IsFeatureSymmetry (phi : iota → X → ℝ) (g : X → X) (O : Matrix iota iota ℝ) : Prop :=
  O.transpose * O = 1 ∧ ∀ j x, phi j (g x) = ∑ i, O j i * phi i x

/-- **The feature kernel is invariant under every feature symmetry.** -/
theorem featureKernel_featureSymmetry {phi : iota → X → ℝ} {g : X → X}
    {O : Matrix iota iota ℝ} (h : IsFeatureSymmetry phi g O) (x y : X) :
    featureKernel phi (g x) (g y) = featureKernel phi x y := by
  obtain ⟨hO, hcomp⟩ := h
  unfold featureKernel
  have hexpand : ∀ j : iota, phi j (g x) * phi j (g y) =
      ∑ i, ∑ l, (O j i * O j l) * (phi i x * phi l y) := by
    intro j
    rw [hcomp j x, hcomp j y, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun j _ => hexpand j]
  rw [Finset.sum_comm]
  have hinner : ∀ i : iota, (∑ j, ∑ l, (O j i * O j l) * (phi i x * phi l y)) =
      phi i x * phi i y := by
    intro i
    rw [Finset.sum_comm]
    have hcol : ∀ l : iota, (∑ j, (O j i * O j l) * (phi i x * phi l y)) =
        (if i = l then (1 : ℝ) else 0) * (phi i x * phi l y) := by
      intro l
      rw [← Finset.sum_mul]
      congr 1
      have hval : (O.transpose * O) i l = ∑ j, O j i * O j l := by
        simp [Matrix.mul_apply, Matrix.transpose_apply]
      rw [← hval, hO]
      simp [Matrix.one_apply]
    rw [Finset.sum_congr rfl fun l _ => hcol l]
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact Finset.sum_congr rfl fun i _ => hinner i

/-- **Under a transitive family of feature symmetries the diagonal is constant.** -/
theorem featureKernel_diag_const_of_transitive {phi : iota → X → ℝ}
    (hsym : ∀ x y : X, ∃ (g : X → X) (O : Matrix iota iota ℝ),
      IsFeatureSymmetry phi g O ∧ g x = y) (x y : X) :
    featureKernel phi x x = featureKernel phi y y := by
  obtain ⟨g, O, hg, hgx⟩ := hsym x y
  rw [← hgx, featureKernel_featureSymmetry hg x x]

/-- **`(8c)`.**  Under a transitive measure-preserving symmetry the leverage is exactly the number
of centred modes. -/
theorem featureKernel_diag_eq_card_of_transitive [Fintype X] {phi : iota → X → ℝ}
    (pi : X → ℝ) (hpi : ∑ x, pi x = 1) (hortho : ∀ j, ∑ x, pi x * phi j x ^ (2 : ℕ) = 1)
    (hsym : ∀ x y : X, ∃ (g : X → X) (O : Matrix iota iota ℝ),
      IsFeatureSymmetry phi g O ∧ g x = y) (x : X) :
    featureKernel phi x x = (Fintype.card iota : ℝ) :=
  featureKernel_diag_eq_card_of_const phi pi hpi hortho
    (fun y => (featureKernel_diag_const_of_transitive hsym y x))

/-- **`(8c)`, the resolvent form.** -/
theorem abs_spectralResolventKernel_le_card [Fintype X] {phi : iota → X → ℝ}
    {lam : iota → ℝ} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hlam : ∀ j, |lam j| ≤ 1)
    (pi : X → ℝ) (hpi : ∑ x, pi x = 1) (hortho : ∀ j, ∑ x, pi x * phi j x ^ (2 : ℕ) = 1)
    (hsym : ∀ x y : X, ∃ (g : X → X) (O : Matrix iota iota ℝ),
      IsFeatureSymmetry phi g O ∧ g x = y) (x y : X) :
    |spectralResolventKernel phi lam a x y| ≤ (Fintype.card iota : ℝ) / (1 - a) :=
  abs_spectralResolventKernel_le ha ha1 hlam
    (fun z => le_of_eq (featureKernel_diag_eq_card_of_transitive pi hpi hortho hsym z)) x y

end Transitive

end

end GaloisForLFunctions.HTGeometry
