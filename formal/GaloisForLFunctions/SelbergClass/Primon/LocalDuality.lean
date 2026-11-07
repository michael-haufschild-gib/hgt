import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
import GaloisForLFunctions.HTGeometry.ChebyshevSpectralPacketGenerating

/-!
# Formal boson–fermion duality for quadratic local factors

The reciprocal relation of Hartnoll–Yang, arXiv:2502.02661v2, (78) and (100),
holds coefficientwise without convergence or temperedness assumptions. The
bosonic series is the existing quadratic-response hierarchy; its fermionic
inverse has only three terms. The same identity persists for every finite
collection of modes and identifies the centered Chebyshev trace numerator.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section
variable {R : Type*} [CommRing R]

/-- Bosonic occupation series with trace `c` and determinant `d`. -/
def bosonSeries (c d : R) : PowerSeries R :=
  PowerSeries.mk (quadraticResponseCoeff (-c) d)

/-- Fermionic signed occupation series: vacuum, two charged states, filled pair. -/
def fermionSeries (c d : R) : PowerSeries R :=
  1 - PowerSeries.X * PowerSeries.C c + PowerSeries.X ^ 2 * PowerSeries.C d

/-- Exact local cancellation of bosonic and fermionic occupation series. -/
theorem fermionSeries_mul_bosonSeries (c d : R) :
    fermionSeries c d * bosonSeries c d = 1 := by
  have he : fermionSeries c d * bosonSeries c d =
      bosonSeries c d - PowerSeries.X * (PowerSeries.C c * bosonSeries c d) +
        PowerSeries.X * (PowerSeries.X * (PowerSeries.C d * bosonSeries c d)) := by
    unfold fermionSeries
    ring
  rw [he]
  apply PowerSeries.ext
  intro n
  rw [map_add, map_sub]
  cases n with
  | zero => simp [bosonSeries, PowerSeries.coeff_zero_X_mul]
  | succ n =>
    cases n with
    | zero => simp [bosonSeries, PowerSeries.coeff_succ_X_mul]
    | succ n =>
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
        bosonSeries, PowerSeries.coeff_mk, quadraticResponseCoeff_add_two, neg_neg]
      simp

/-- Chiral fermionic factors multiply to the quadratic signed occupation series. -/
theorem fermionSeries_chiral (a b : R) :
    fermionSeries (a + b) (a * b) =
      (1 - PowerSeries.X * PowerSeries.C a) *
        (1 - PowerSeries.X * PowerSeries.C b) := by
  simp only [fermionSeries, map_add, map_mul]
  ring

/-- Any finite collection of modes retains exact boson–fermion cancellation. -/
theorem finite_modes_duality {ι : Type*} (s : Finset ι) (c d : ι → R) :
    (∏ i ∈ s, fermionSeries (c i) (d i)) *
      (∏ i ∈ s, bosonSeries (c i) (d i)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  simp only [fermionSeries_mul_bosonSeries, Finset.prod_const_one]

/-- The centered spectral Chebyshev trace is the bosonic local factor with
the universal numerator `1-X²`. -/
theorem centered_chebyshev_eq_boson (x : ℂ) :
    2 * _root_.HTGeometry.chebyshevNodeSeries x - 1 =
      (1 - PowerSeries.X ^ 2) * bosonSeries (2 * x) 1 := by
  have h := _root_.HTGeometry.chebyshevNodeSeries_centered_equation x
  have hD : (1 : PowerSeries ℂ) - PowerSeries.X * PowerSeries.C (2 * x) +
      PowerSeries.X ^ 2 = fermionSeries (2 * x) 1 := by
    simp [fermionSeries]
  rw [hD] at h
  calc
    _ = (fermionSeries (2 * x) 1 * bosonSeries (2 * x) 1) *
        (2 * _root_.HTGeometry.chebyshevNodeSeries x - 1) := by
      rw [fermionSeries_mul_bosonSeries, one_mul]
    _ = (fermionSeries (2 * x) 1 *
        (2 * _root_.HTGeometry.chebyshevNodeSeries x - 1)) *
          bosonSeries (2 * x) 1 := by ring
    _ = _ := by rw [h]

/-- Every finite spectral packet is a weighted superposition of bosonic local
factors with the same fermionic numerator. -/
theorem centered_packet_eq_boson {r : ℕ} (lam w : Fin r → ℂ) :
    2 * packetChebyshevSeries lam w - PowerSeries.C (∑ j, w j * lam j) =
      (1 - PowerSeries.X ^ 2) *
        ∑ j, PowerSeries.C (w j * lam j) * bosonSeries (2 * (1 - 2 * lam j)) 1 := by
  rw [packetChebyshevSeries_centered, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [centered_chebyshev_eq_boson]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
