import GaloisForLFunctions.RHTower.EulerSquarefreeWickArtinInteractionNoGo
import GaloisForLFunctions.RHTower.SeamFluxCompletion
import GaloisForLFunctions.RHTower.DirichletLZerosInfinite

/-!
# Regular-orbit completion of the Euler--Wick residue interaction

The scalar landing obstruction is sharp: the interaction character cannot be read faithfully by
an invariant scalar, but all four quadratic Fourier sectors admit a coefficient-faithful landing in
the regular representation.  Its inverse Fourier transform sends every literal prime-power residue
profile to exactly one of four cells, without selecting a divisor.

The completed Fourier coordinates are the logarithmic derivatives of Xi and the completed
Dirichlet L-functions for the mod-3, mod-4, and product characters.  Summing the four cells recovers
the Xi logarithmic derivative exactly; the anchored reader recovers the completed virtual Artin
interaction.

The real Fourier space also carries a canonical split form with signs `(+,-,-,+)`.  Literal residue
packets are null, the joint interaction axis is positive, and marginal axes are negative.  More
strongly, the norm of nonnegative cell weights is `8(ad+bc)`, exposing opposite-cell pairing as the
positive interaction invariant.  This is an exact vector landing and polarization law, not yet a
divisor-orientation theorem.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fourier coordinates for the regular representation of the two quadratic residue gauges. -/
@[ext]
structure QuadraticResidueFourierCoordinates (K : Type*) where
  vacuum : K
  fst : K
  snd : K
  joint : K

/-- Inverse Fourier transform from four character sectors to one residue cell. -/
def quadraticResidueRegularCellPacket
    (A : QuadraticResidueFourierCoordinates ℂ) (x y : Fin 2) : ℂ :=
  (A.vacuum + finTwoAnchoredSign x * A.fst + finTwoAnchoredSign y * A.snd +
      finTwoAnchoredSign x * finTwoAnchoredSign y * A.joint) / 4

/-- Fourier coordinates of a scalar packet supported at one literal residue cell. -/
def quadraticResiduePureDepthCoordinates
    (z : ℂ) (x y : Fin 2) : QuadraticResidueFourierCoordinates ℂ where
  vacuum := z
  fst := finTwoAnchoredSign x * z
  snd := finTwoAnchoredSign y * z
  joint := finTwoAnchoredSign x * finTwoAnchoredSign y * z

/-- Actual unit-character coordinates of one prime-power depth. -/
def quadraticResidueGaugeDepthCoordinates
    (z : ℂ) (k : ℕ) (w : QuadraticResidueGaugeSpace) :
    QuadraticResidueFourierCoordinates ℂ where
  vacuum := z
  fst := quadraticCharacterThreeUnit w.1 ^ k * z
  snd := quadraticCharacterFourUnit w.2 ^ k * z
  joint := (quadraticCharacterThreeUnit w.1 * quadraticCharacterFourUnit w.2) ^ k * z

/-- Even exterior-degree character of the two quadratic gauge lines. -/
def quadraticResidueFockEvenDepthCharacter
    (k : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) : ℂ :=
  1 + (quadraticCharacterThreeUnit w.1.1 *
    quadraticCharacterFourUnit w.1.2) ^ k

/-- Odd exterior-degree character of the two quadratic gauge lines. -/
def quadraticResidueFockOddDepthCharacter
    (k : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) : ℂ :=
  quadraticCharacterThreeUnit w.1.1 ^ k +
    quadraticCharacterFourUnit w.1.2 ^ k

/-- EWQ's virtual Euler coefficient is the supercharacter of the two-line exterior Fock space. -/
theorem quadraticResidueFock_supercharacter_eq_virtualEulerDepthCoefficient
    (k : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) :
    quadraticResidueFockEvenDepthCharacter k w - quadraticResidueFockOddDepthCharacter k w =
      quadraticResidueVirtualEulerDepthCoefficient k w := by
  simp [quadraticResidueFockEvenDepthCharacter, quadraticResidueFockOddDepthCharacter,
    quadraticResidueVirtualEulerDepthCoefficient]
  ring

private theorem pow_sq_eq_one_of_sq_eq_one {a : ℂ} (ha : a ^ (2 : ℕ) = 1) (k : ℕ) :
    (a ^ k) ^ (2 : ℕ) = 1 := by
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, ha, one_pow]

private theorem exists_finTwoAnchoredSign_eq_of_sq_eq_one {a : ℂ} (ha : a ^ (2 : ℕ) = 1) :
    ∃ x : Fin 2, finTwoAnchoredSign x = a := by
  rcases sq_eq_one_iff.mp ha with ha | ha
  · exact ⟨1, by simpa using ha.symm⟩
  · exact ⟨0, by simpa using ha.symm⟩

/-- Every literal quadratic residue depth is one of the four regular-representation cells. -/
theorem exists_pureDepth_eq_quadraticResidueGaugeDepthCoordinates
    (z : ℂ) (k : ℕ) (w : QuadraticResidueGaugeSpace) :
    ∃ x y : Fin 2,
      quadraticResiduePureDepthCoordinates z x y =
        quadraticResidueGaugeDepthCoordinates z k w := by
  obtain ⟨x, hx⟩ := exists_finTwoAnchoredSign_eq_of_sq_eq_one
    (pow_sq_eq_one_of_sq_eq_one (quadraticCharacterThreeUnit_sq w.1) k)
  obtain ⟨y, hy⟩ := exists_finTwoAnchoredSign_eq_of_sq_eq_one
    (pow_sq_eq_one_of_sq_eq_one (quadraticCharacterFourUnit_sq w.2) k)
  refine ⟨x, y, ?_⟩
  apply QuadraticResidueFourierCoordinates.ext <;>
    simp [quadraticResiduePureDepthCoordinates,
      quadraticResidueGaugeDepthCoordinates, hx, hy, mul_pow]

/-- Inverse Fourier transform sends a pure residue profile to its unique cell. -/
theorem quadraticResidueRegularCellPacket_pureDepth
    (z : ℂ) (x y u v : Fin 2) :
    quadraticResidueRegularCellPacket (quadraticResiduePureDepthCoordinates z x y) u v =
      if u = x ∧ v = y then z else 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;>
    simp [quadraticResidueRegularCellPacket, quadraticResiduePureDepthCoordinates,
      finTwoAnchoredSign] <;> ring

/-- Cell augmentation recovers the vacuum Fourier coordinate. -/
theorem sum_quadraticResidueRegularCellPacket
    (A : QuadraticResidueFourierCoordinates ℂ) :
    (∑ x : Fin 2, ∑ y : Fin 2, quadraticResidueRegularCellPacket A x y) = A.vacuum := by
  simp [quadraticResidueRegularCellPacket, finTwoAnchoredSign]
  ring

/-- First signed cell sum recovers the first marginal Fourier coordinate. -/
theorem sum_fst_mul_quadraticResidueRegularCellPacket
    (A : QuadraticResidueFourierCoordinates ℂ) :
    (∑ x : Fin 2, ∑ y : Fin 2,
      finTwoAnchoredSign x * quadraticResidueRegularCellPacket A x y) = A.fst := by
  simp [quadraticResidueRegularCellPacket, finTwoAnchoredSign]
  ring

/-- Second signed cell sum recovers the second marginal Fourier coordinate. -/
theorem sum_snd_mul_quadraticResidueRegularCellPacket
    (A : QuadraticResidueFourierCoordinates ℂ) :
    (∑ x : Fin 2, ∑ y : Fin 2,
      finTwoAnchoredSign y * quadraticResidueRegularCellPacket A x y) = A.snd := by
  simp [quadraticResidueRegularCellPacket, finTwoAnchoredSign]
  ring

/-- Joint signed cell sum recovers the interaction Fourier coordinate. -/
theorem sum_joint_mul_quadraticResidueRegularCellPacket
    (A : QuadraticResidueFourierCoordinates ℂ) :
    (∑ x : Fin 2, ∑ y : Fin 2,
      finTwoAnchoredSign x * finTwoAnchoredSign y *
        quadraticResidueRegularCellPacket A x y) = A.joint := by
  simp [quadraticResidueRegularCellPacket, finTwoAnchoredSign]
  ring

/-- Anchored mixed reader on the full regular representation. -/
def quadraticResidueAnchoredRegularReader
    (A : QuadraticResidueFourierCoordinates ℂ) : ℂ :=
  ∑ x : Fin 2, ∑ y : Fin 2,
    (1 - finTwoAnchoredSign x) * (1 - finTwoAnchoredSign y) *
      quadraticResidueRegularCellPacket A x y

/-- The anchored reader is the four-sector inclusion--exclusion functional. -/
theorem quadraticResidueAnchoredRegularReader_eq
    (A : QuadraticResidueFourierCoordinates ℂ) :
    quadraticResidueAnchoredRegularReader A =
      A.vacuum - A.fst - A.snd + A.joint := by
  simp [quadraticResidueAnchoredRegularReader, quadraticResidueRegularCellPacket,
    finTwoAnchoredSign]
  ring

/-- On a literal depth packet the anchored reader is the exact two-gauge interaction. -/
theorem quadraticResidueAnchoredRegularReader_pureDepth
    (z : ℂ) (x y : Fin 2) :
    quadraticResidueAnchoredRegularReader (quadraticResiduePureDepthCoordinates z x y) =
      z * (1 - finTwoAnchoredSign x) * (1 - finTwoAnchoredSign y) := by
  rw [quadraticResidueAnchoredRegularReader_eq]
  simp [quadraticResiduePureDepthCoordinates]
  ring

/-- The four completed logarithmic-derivative channels in the regular residue representation. -/
def eulerSquarefreeWickCompletedFluxCoordinates (s : ℂ) :
    QuadraticResidueFourierCoordinates ℂ where
  vacuum := -logDeriv _root_.RHTower.xi s
  fst := -logDeriv (DirichletCharacter.completedLFunction quadraticCharacterThree) s
  snd := -logDeriv
    (DirichletCharacter.completedLFunction RHTower.quadraticCharacterFour) s
  joint := -logDeriv (DirichletCharacter.completedLFunction quadraticCharacterTwelve) s

/-- Completed regular-orbit landing retaining all four gauge sectors. -/
def eulerSquarefreeWickCompletedRegularFlux (s : ℂ) (x y : Fin 2) : ℂ :=
  quadraticResidueRegularCellPacket (eulerSquarefreeWickCompletedFluxCoordinates s) x y

/-- The gauge-invariant augmentation of the completed regular orbit is exactly the Xi flux. -/
theorem sum_eulerSquarefreeWickCompletedRegularFlux (s : ℂ) :
    (∑ x : Fin 2, ∑ y : Fin 2, eulerSquarefreeWickCompletedRegularFlux s x y) =
      -logDeriv _root_.RHTower.xi s := by
  simpa [eulerSquarefreeWickCompletedRegularFlux,
    eulerSquarefreeWickCompletedFluxCoordinates] using
    sum_quadraticResidueRegularCellPacket (eulerSquarefreeWickCompletedFluxCoordinates s)

/-- The anchored mixed reader is the completed four-sector interaction flux. -/
theorem anchored_eulerSquarefreeWickCompletedRegularFlux (s : ℂ) :
    quadraticResidueAnchoredRegularReader (eulerSquarefreeWickCompletedFluxCoordinates s) =
      -logDeriv _root_.RHTower.xi s +
        logDeriv (DirichletCharacter.completedLFunction quadraticCharacterThree) s +
        logDeriv (DirichletCharacter.completedLFunction RHTower.quadraticCharacterFour) s -
        logDeriv (DirichletCharacter.completedLFunction quadraticCharacterTwelve) s := by
  rw [quadraticResidueAnchoredRegularReader_eq]
  simp [eulerSquarefreeWickCompletedFluxCoordinates]
  ring

/-- Split Fourier form: vacuum and interaction are positive, marginal axes are negative. -/
def quadraticResidueKreinForm
    (A B : QuadraticResidueFourierCoordinates ℝ) : ℝ :=
  A.vacuum * B.vacuum - A.fst * B.fst - A.snd * B.snd + A.joint * B.joint

/-- Real Fourier coordinates of a packet supported at one literal residue cell. -/
def quadraticResiduePureRealDepthCoordinates
    (z : ℝ) (x y : Fin 2) : QuadraticResidueFourierCoordinates ℝ where
  vacuum := z
  fst := (finTwoAnchoredSign x).re * z
  snd := (finTwoAnchoredSign y).re * z
  joint := (finTwoAnchoredSign x).re * (finTwoAnchoredSign y).re * z

/-- Every literal real prime-power cell is null for the split interaction form. -/
theorem quadraticResidueKreinForm_pureDepth_null
    (z : ℝ) (x y : Fin 2) :
    quadraticResidueKreinForm (quadraticResiduePureRealDepthCoordinates z x y)
      (quadraticResiduePureRealDepthCoordinates z x y) = 0 := by
  fin_cases x <;> fin_cases y <;>
    simp [quadraticResidueKreinForm, quadraticResiduePureRealDepthCoordinates,
      finTwoAnchoredSign]

/-- Real cell weights transformed to the four quadratic Fourier sectors. -/
def quadraticResidueRealCellFourierCoordinates
    (a b c d : ℝ) : QuadraticResidueFourierCoordinates ℝ where
  vacuum := a + b + c + d
  fst := a + b - c - d
  snd := a - b + c - d
  joint := a - b - c + d

/-- The Krein norm of a real residue packet is exactly its opposite-cell pairing. -/
theorem quadraticResidueKreinForm_realCellFourierCoordinates_self
    (a b c d : ℝ) :
    quadraticResidueKreinForm (quadraticResidueRealCellFourierCoordinates a b c d)
      (quadraticResidueRealCellFourierCoordinates a b c d) = 8 * (a * d + b * c) := by
  simp [quadraticResidueKreinForm, quadraticResidueRealCellFourierCoordinates]
  ring

/-- Nonnegative residue sources occupy the nonnegative cone of the interaction polarization. -/
theorem quadraticResidueKreinForm_realCellFourierCoordinates_nonneg
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ quadraticResidueKreinForm (quadraticResidueRealCellFourierCoordinates a b c d)
      (quadraticResidueRealCellFourierCoordinates a b c d) := by
  rw [quadraticResidueKreinForm_realCellFourierCoordinates_self]
  positivity

/-- Pure interaction Fourier axis. -/
def quadraticResidueJointAxis (z : ℝ) : QuadraticResidueFourierCoordinates ℝ where
  vacuum := 0
  fst := 0
  snd := 0
  joint := z

theorem quadraticResidueKreinForm_jointAxis_self (z : ℝ) :
    quadraticResidueKreinForm (quadraticResidueJointAxis z)
      (quadraticResidueJointAxis z) = z ^ (2 : ℕ) := by
  simp [quadraticResidueKreinForm, quadraticResidueJointAxis]
  ring

/-- The nonzero interaction axis is strictly positive. -/
theorem quadraticResidueKreinForm_jointAxis_pos {z : ℝ} (hz : z ≠ 0) :
    0 < quadraticResidueKreinForm (quadraticResidueJointAxis z)
      (quadraticResidueJointAxis z) := by
  rw [quadraticResidueKreinForm_jointAxis_self]
  exact sq_pos_of_ne_zero hz

/-- First marginal Fourier axis. -/
def quadraticResidueFstAxis (z : ℝ) : QuadraticResidueFourierCoordinates ℝ where
  vacuum := 0
  fst := z
  snd := 0
  joint := 0

/-- Second marginal Fourier axis. -/
def quadraticResidueSndAxis (z : ℝ) : QuadraticResidueFourierCoordinates ℝ where
  vacuum := 0
  fst := 0
  snd := z
  joint := 0

theorem quadraticResidueKreinForm_fstAxis_self (z : ℝ) :
    quadraticResidueKreinForm (quadraticResidueFstAxis z)
      (quadraticResidueFstAxis z) = -(z ^ (2 : ℕ)) := by
  simp [quadraticResidueKreinForm, quadraticResidueFstAxis]
  ring

theorem quadraticResidueKreinForm_sndAxis_self (z : ℝ) :
    quadraticResidueKreinForm (quadraticResidueSndAxis z)
      (quadraticResidueSndAxis z) = -(z ^ (2 : ℕ)) := by
  simp [quadraticResidueKreinForm, quadraticResidueSndAxis]
  ring

/-- Every nonzero first-marginal vector is strictly negative. -/
theorem quadraticResidueKreinForm_fstAxis_neg {z : ℝ} (hz : z ≠ 0) :
    quadraticResidueKreinForm (quadraticResidueFstAxis z)
      (quadraticResidueFstAxis z) < 0 := by
  rw [quadraticResidueKreinForm_fstAxis_self]
  exact neg_neg_of_pos (sq_pos_of_ne_zero hz)

/-- Every nonzero second-marginal vector is strictly negative. -/
theorem quadraticResidueKreinForm_sndAxis_neg {z : ℝ} (hz : z ≠ 0) :
    quadraticResidueKreinForm (quadraticResidueSndAxis z)
      (quadraticResidueSndAxis z) < 0 := by
  rw [quadraticResidueKreinForm_sndAxis_self]
  exact neg_neg_of_pos (sq_pos_of_ne_zero hz)

end

end GaloisForLFunctions.RHTower
