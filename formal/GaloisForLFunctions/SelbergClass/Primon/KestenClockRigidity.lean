import GaloisForLFunctions.HTGeometry.LinearAlgebra.ScalingNilpotence
import GaloisForLFunctions.HTGeometry.Holonomy.FiniteAlgebraTransport
import GaloisForLFunctions.SelbergClass.Primon.KestenFiniteGreen

/-!
# Positive scaling rigidity of finite Kesten clocks

Neither a finite prime Green kernel nor its precision matrix can be rescaled
by a nontrivial positive factor under an algebra endomorphism. In particular,
invertible transport around a loop preserves the time scale. The source
matrices are already positive definite, so no additional spectral input is
needed for the finite-algebra form of Alexa's no-scalar-monodromy mechanism.
On a connected graph of compatible prime Green generators, all edge scales
come from a positive global calibration and the normalized generators are
transported without rescaling. Flatness and reverse-edge reciprocity are
conclusions.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass.Primon
open GaloisForLFunctions.HTGeometry

/-- Every positive scaling of the actual finite Green matrix by an algebra map is one. -/
theorem kestenFiniteGreen_scale_rigid (p : Nat.Primes) (n : ℕ)
    (e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (hq : 0 < q) (hscale : e (kestenFiniteGreen p n) = q • kestenFiniteGreen p n) :
    q = 1 :=
  real_algHom_unit_scale_rigid e (kestenFiniteGreen p n) (posDef_kestenFiniteGreen p n).isUnit
    q hq hscale

/-- The same rigidity holds for the actual finite precision matrix. -/
theorem kestenFiniteGreen_inverse_scale_rigid (p : Nat.Primes) (n : ℕ)
    (e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (hq : 0 < q)
    (hscale : e ((kestenFiniteGreen p n)⁻¹) = q • (kestenFiniteGreen p n)⁻¹) : q = 1 :=
  real_algHom_unit_scale_rigid e (kestenFiniteGreen p n)⁻¹
    (posDef_kestenFiniteGreen_inverse p n).isUnit q hq hscale

/-- Compatible positive edge scales have trivial product around every closed walk. -/
theorem kestenNetwork_scalar_holonomy {V : Type*} {G : SimpleGraph V} (n : ℕ)
    (prime : V → Nat.Primes) (c : V → V → ℝˣ)
    (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (t : V → V → (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (ht : ∀ {u v}, G.Adj u v → t u v (kestenFiniteGreen (prime v) n) =
      (c u v : ℝ) • kestenFiniteGreen (prime u) n) : ClockCalibrationFlat G c :=
  clockCalibrationFlat_of_algebra_transport (fun v => kestenFiniteGreen (prime v) n)
    (fun v => (posDef_kestenFiniteGreen (prime v) n).isUnit.not_isNilpotent) c hc t ht

/-- A chosen basepoint fixes a unique positive gauge with exactly transported generators. -/
theorem kestenNetwork_positive_gauge {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (root : V) (n : ℕ) (prime : V → Nat.Primes) (c : V → V → ℝˣ)
    (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (t : V → V → (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (ht : ∀ {u v}, G.Adj u v → t u v (kestenFiniteGreen (prime v) n) =
      (c u v : ℝ) • kestenFiniteGreen (prime u) n) :
    ∃! g : V → ℝˣ, g root = 1 ∧ (∀ v, 0 < (g v : ℝ)) ∧
      (∀ {u v}, G.Adj u v → c u v = (g u)⁻¹ * g v) ∧
      ∀ {u v}, G.Adj u v →
        t u v ((g v)⁻¹ • kestenFiniteGreen (prime v) n) =
          (g u)⁻¹ • kestenFiniteGreen (prime u) n := by
  obtain ⟨g, ⟨hgroot, hgpos, hg⟩, huniq⟩ :=
    existsUnique_positiveClockPotential_of_algebra_transport hG root
    (fun v => kestenFiniteGreen (prime v) n)
    (fun v => (posDef_kestenFiniteGreen (prime v) n).isUnit.not_isNilpotent) c hc t ht
  exact ⟨g, ⟨hgroot, hgpos, hg,
    algebraTransport_normalized (fun v => kestenFiniteGreen (prime v) n) c t ht g hg⟩,
    fun h hh => huniq h ⟨hh.1, hh.2.1, hh.2.2.1⟩⟩

end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenFiniteGreen_scale_rigid
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenFiniteGreen_inverse_scale_rigid
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenNetwork_scalar_holonomy
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenNetwork_positive_gauge
