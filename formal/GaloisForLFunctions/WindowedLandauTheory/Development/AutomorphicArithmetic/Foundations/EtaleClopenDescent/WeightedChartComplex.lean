import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedWeightedCech
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Fin.Basic

/-! Chart-dependent normalizations of the coefficients in a joined
Čech complex with a Koszul differential. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

/-- The ring action, homogeneous coordinates, and regular coefficients
on a product of two projective covers. -/
structure WeightedChartSystem (k : Type) (d : ℕ) (S E : Type) [Field k]
    [CommRing S] [Algebra k S] [AddCommGroup E] [Module k E] where
  act : S →ₐ[k] Module.End k E
  X : Fin (d + 1) → Sˣ
  Y : Fin (d + 1) → Sˣ
  R : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Subalgebra k S
  M : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Submodule k E

namespace WeightedChartSystem

variable {k S E : Type} [Field k] [CommRing S] [Algebra k S] [AddCommGroup E] [Module k E]
  {d : ℕ} (T : WeightedChartSystem k d S E) {κ : Type} [LinearOrder κ]

/-- Regularity of chart restrictions and coordinate ratios. -/
structure Good : Prop where
  monoR : ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → T.R I J ≤ T.R I' J'
  monoM : ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → T.M I J ≤ T.M I' J'
  stab : ∀ I J, I.Nonempty → J.Nonempty → ∀ r ∈ T.R I J, ∀ m ∈ T.M I J, T.act r m ∈ T.M I J
  memX : ∀ I J, J.Nonempty → ∀ i ∈ I, ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R I J
  memY : ∀ I J, I.Nonempty → ∀ j ∈ J, ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R I J

/-- Choose a chart for writing affine coordinates on an intersection. -/
def chartIndex (I : Finset (Fin (d + 1))) : Fin (d + 1) :=
  if h : I.Nonempty then I.min' h else 0

theorem chartIndex_mem {I : Finset (Fin (d + 1))} (h : I.Nonempty) : chartIndex I ∈ I := by
  rw [chartIndex, dif_pos h]
  exact Finset.min'_mem _ _

/-- The normalization of a homogeneous weight on a pair of affine charts. -/
def weightUnit (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (l : κ) : Sˣ :=
  T.X i ^ (n l).1 * T.Y j ^ (n l).2

def normalizedWeight (n : κ → ℕ × ℕ) (z : κ → S) (i j : Fin (d + 1)) (l : κ) : S :=
  z l * ((T.weightUnit n i j l)⁻¹ : Sˣ)

/-- A homogeneous weight becomes regular on every affine chart pair. -/
def Admitted (n : κ → ℕ × ℕ) (z : κ → S) : Prop :=
  ∀ i j l, T.normalizedWeight n z i j l ∈ T.R (Singleton.singleton i) (Singleton.singleton j)

abbrev ChartPair (d : ℕ) := Fin (d + 1) ⊕ₗ Fin (d + 1)

abbrev DiagonalIndex (d : ℕ) : Type := Fin (d + 1) ×ₗ Fin (d + 1)

/-- Index the equations comparing every other coordinate with the chosen denominator. -/
def diagonalIndexEmbedding (j : Fin (d + 1)) : Fin d ↪o DiagonalIndex d :=
  OrderEmbedding.ofStrictMono (fun l => toLex (j.succAbove l, j)) fun _ _ hlt =>
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (j.succAboveOrderEmb.strictMono hlt))

/-- One homogeneous equation comparing the two projective coordinate lists. -/
def homogeneousMinor (l : DiagonalIndex d) : S :=
  T.X (ofLex l).1 * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1

/-- The coefficient lattice multiplied by the normalizing unit of a Koszul index set. -/
def scaledCoefficients (n : κ → ℕ × ℕ) (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    Submodule k E :=
  (T.M I J).map (T.act ((∏ l ∈ L, T.weightUnit n (chartIndex I) (chartIndex J) l : Sˣ) : S))

/-- The scaled coefficients vanish unless both chart index sets are nonempty. -/
def mixedCoefficients (n : κ → ℕ × ℕ) (L : Finset κ) (s : Finset (ChartPair d)) :
    Submodule k E :=
  if (lft s).Nonempty ∧ (rgt s).Nonempty then T.scaledCoefficients n (lft s) (rgt s) L else ⊥

/-- Chart deletions have weight one. The right index deletions carry
the Koszul weights. -/
def weights (z : κ → S) (i : ChartPair d ⊕ₗ κ) : Module.End k E :=
  T.act (Sum.elim (fun _ => 1) z (ofLex i))

def complex (n : κ → ℕ × ℕ) (z : κ → S) : Cx k (Finset (ChartPair d ⊕ₗ κ) → E) :=
  acx (fun s => T.mixedCoefficients n (rgt s) (lft s)) (T.weights z)

def columnComplex (n : κ → ℕ × ℕ) (z : κ → S)
    (I J : Finset (Fin (d + 1))) : Cx k (Finset κ → E) :=
  acx (T.scaledCoefficients n I J) (fun l => T.act (z l))

end WeightedChartSystem

end GlobalTheory.WH
