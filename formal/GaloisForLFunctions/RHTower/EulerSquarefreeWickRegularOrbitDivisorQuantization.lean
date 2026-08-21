import GaloisForLFunctions.RHTower.EulerSquarefreeWickOppositeResidueCrossing
import GaloisForLFunctions.HTGeometry.ConstitutiveDivisibleFormationSelection

/-!
# Divisor quantization for Euler--Wick regular-orbit landing

The completed regular-orbit construction is automatically valid for logarithmic fluxes, but a
stronger landing by genuine single-valued meromorphic cell carriers is arithmetic.  Inverse Walsh
transform divides four Fourier-sector residues by four, while every meromorphic logarithmic
derivative has integral residue.  Therefore cell orders must lie in the integral Hadamard lattice.

This module proves the exact rank-two lattice reconstruction and its sharp pure-vacuum
consequence: if the three auxiliary Dirichlet-L sectors are units at a point, cell landing forces
the Xi order to be divisible by four.  For a rank-`r` binary gauge cube the required divisor is
`2^r`.  Integral landings at every rank annihilate any finite integer order.  The analytic version
uses the corpus unbounded-root theorem to show that genuine meromorphic binary regular-orbit roots
at every rank annihilate the local divisor.

Thus unbounded coefficient-faithful cell descent would exclude every strict-right Xi divisor once
auxiliary product-character orders are removed.  Existence of those cell roots, or sufficient
pointwise avoidance of auxiliary L-zeros, remains the analytic EWQ frontier.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Integral version of the anchored sign on a two-cell gauge. -/
def finTwoDivisorSign (x : Fin 2) : ℤ :=
  if x = 1 then 1 else -1

/-- Numerator of one inverse-Walsh divisor cell before division by four. -/
def quadraticResidueDivisorCellNumerator
    (m : QuadraticResidueFourierCoordinates ℤ) (x y : Fin 2) : ℤ :=
  m.vacuum + finTwoDivisorSign x * m.fst + finTwoDivisorSign y * m.snd +
    finTwoDivisorSign x * finTwoDivisorSign y * m.joint

/-- Integer cell orders realizing the inverse Fourier transform of four sector orders. -/
def QuadraticResidueCellOrderLanding
    (m : QuadraticResidueFourierCoordinates ℤ) (c : Fin 2 → Fin 2 → ℤ) : Prop :=
  ∀ x y, 4 * c x y = quadraticResidueDivisorCellNumerator m x y

/-- Integral cell orders recover the vacuum divisor order. -/
theorem quadraticResidueCellOrderLanding_vacuum
    {m : QuadraticResidueFourierCoordinates ℤ} {c : Fin 2 → Fin 2 → ℤ}
    (h : QuadraticResidueCellOrderLanding m c) :
    c 0 0 + c 0 1 + c 1 0 + c 1 1 = m.vacuum := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [quadraticResidueDivisorCellNumerator, finTwoDivisorSign] at h00 h01 h10 h11
  omega

/-- Integral cell orders recover the first marginal divisor order. -/
theorem quadraticResidueCellOrderLanding_fst
    {m : QuadraticResidueFourierCoordinates ℤ} {c : Fin 2 → Fin 2 → ℤ}
    (h : QuadraticResidueCellOrderLanding m c) :
    -c 0 0 - c 0 1 + c 1 0 + c 1 1 = m.fst := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [quadraticResidueDivisorCellNumerator, finTwoDivisorSign] at h00 h01 h10 h11
  omega

/-- Integral cell orders recover the second marginal divisor order. -/
theorem quadraticResidueCellOrderLanding_snd
    {m : QuadraticResidueFourierCoordinates ℤ} {c : Fin 2 → Fin 2 → ℤ}
    (h : QuadraticResidueCellOrderLanding m c) :
    -c 0 0 + c 0 1 - c 1 0 + c 1 1 = m.snd := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [quadraticResidueDivisorCellNumerator, finTwoDivisorSign] at h00 h01 h10 h11
  omega

/-- Integral cell orders recover the joint interaction divisor order. -/
theorem quadraticResidueCellOrderLanding_joint
    {m : QuadraticResidueFourierCoordinates ℤ} {c : Fin 2 → Fin 2 → ℤ}
    (h : QuadraticResidueCellOrderLanding m c) :
    c 0 0 - c 0 1 - c 1 0 + c 1 1 = m.joint := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [quadraticResidueDivisorCellNumerator, finTwoDivisorSign] at h00 h01 h10 h11
  omega

/-- If all auxiliary Fourier sectors are units, a genuine cell landing forces four-divisibility
of the vacuum/Xi divisor order. -/
theorem four_dvd_vacuum_of_quadraticResidueCellOrderLanding_pure
    {m : QuadraticResidueFourierCoordinates ℤ} {c : Fin 2 → Fin 2 → ℤ}
    (h : QuadraticResidueCellOrderLanding m c)
    (hfst : m.fst = 0) (hsnd : m.snd = 0) (hjoint : m.joint = 0) :
    (4 : ℤ) ∣ m.vacuum := by
  refine ⟨c 1 1, ?_⟩
  have h11 := h 1 1
  simp [quadraticResidueDivisorCellNumerator, finTwoDivisorSign,
    hfst, hsnd, hjoint] at h11
  omega

/-- Pure-vacuum integral landing on a rank-`r` binary gauge cube. -/
def BinaryPureVacuumCellOrderLanding (r : ℕ) (m : ℤ) : Prop :=
  ∃ c : (Fin r → Fin 2) → ℤ, ∀ x, ((2 ^ r : ℕ) : ℤ) * c x = m

/-- A rank-`r` pure-vacuum landing forces `2^r` to divide the vacuum order. -/
theorem pow_two_dvd_of_binaryPureVacuumCellOrderLanding
    {r : ℕ} {m : ℤ} (h : BinaryPureVacuumCellOrderLanding r m) :
    (((2 ^ r : ℕ) : ℤ)) ∣ m := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c (fun _ => 1), ?_⟩
  exact (hc (fun _ => 1)).symm

private theorem nat_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
      omega

/-- Landings on binary cubes of every rank annihilate the integer vacuum charge. -/
theorem vacuumOrder_eq_zero_of_all_binaryPureVacuumCellOrderLandings
    (m : ℤ) (h : ∀ r : ℕ, BinaryPureVacuumCellOrderLanding r m) :
    m = 0 := by
  apply GaloisForLFunctions.HTGeometry.int_eq_zero_of_unbounded_natCast_dvd
  intro N
  exact ⟨2 ^ N, nat_le_two_pow_self N,
    pow_two_dvd_of_binaryPureVacuumCellOrderLanding (h N)⟩

/-- A nonzero finite vacuum order cannot possess integral cell landings at every binary rank. -/
theorem not_all_binaryPureVacuumCellOrderLandings_of_ne_zero
    {m : ℤ} (hm : m ≠ 0) :
    ¬ ∀ r : ℕ, BinaryPureVacuumCellOrderLanding r m := by
  intro h
  exact hm (vacuumOrder_eq_zero_of_all_binaryPureVacuumCellOrderLandings m h)

/-- Genuine meromorphic root landing for one rank of a binary regular orbit. -/
def BinaryRegularOrbitRootLandingAt
    (R : ℂ → ℂ) (z : ℂ) (r : ℕ) : Prop :=
  ∃ G : ℂ → ℂ, MeromorphicAt G z ∧ G ^ (2 ^ r) = R

/-- Meromorphic binary regular-orbit roots of every rank annihilate the local divisor order. -/
theorem meromorphicOrderAt_eq_zero_of_all_binaryRegularOrbitRootLandings
    (R : ℂ → ℂ) (z : ℂ) (hfinite : meromorphicOrderAt R z ≠ ⊤)
    (h : ∀ r : ℕ, BinaryRegularOrbitRootLandingAt R z r) :
    meromorphicOrderAt R z = 0 := by
  apply GaloisForLFunctions.HTGeometry.meromorphicOrderAt_eq_zero_of_unbounded_roots
    R z hfinite
  intro N
  obtain ⟨G, hG, hpow⟩ := h N
  exact ⟨2 ^ N, nat_le_two_pow_self N, G, hG, hpow⟩

end

end GaloisForLFunctions.RHTower
