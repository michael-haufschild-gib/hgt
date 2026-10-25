import GaloisForLFunctions.BiarithmeticGeometry.CofactorGraphDomain
import GaloisForLFunctions.BiarithmeticGeometry.PronicWienerCoordinates
import GaloisForLFunctions.HTGeometry.LatticeL2Shift

/-!
# Finite source horizons in the completed pronic representation

Every finite arithmetic horizon has a finite-support pronic extension. The
completed representation therefore proves exact cofactor composition for
arbitrary source rows, without a growth or summability premise on those rows.
-/

noncomputable section
open Finset
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Reindex the graph coordinates by their positive cell labels. -/
def pronicPositiveCoordinates : PronicCoordinateSpace ≃ₗᵢ[ℂ] PronicHilbertSpace :=
  lpDomCongr (p := 2) (by norm_num) Equiv.pnatEquivNat

theorem pronicPositiveCoordinates_apply (w : PronicCoordinateSpace) (n : ℕ) :
    pronicPositiveCoordinates w ⟨n + 1, by omega⟩ = w n := rfl

private def pronicFiniteCoordinates (v : ℕ → ℂ) (N : ℕ) : PronicCoordinateSpace :=
  ⟨fun n => if n < N then v (n + 1) / (pronicCoordinateRoot (n + 1) : ℂ) else 0,
    memℓp_gen (by
      have hs : Summable (fun n : ℕ =>
          ‖if n < N then v (n + 1) / (pronicCoordinateRoot (n + 1) : ℂ) else 0‖ ^ 2) := by
        apply summable_of_ne_finset_zero (s := range N)
        intro n hn
        simp only [mem_range] at hn
        simp only [if_neg hn, norm_zero, zero_pow (by omega : 2 ≠ 0)]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩

/-- Extend a finite positive source horizon by zero in normalized pronic coordinates. -/
def pronicFiniteExtension (v : ℕ → ℂ) (N : ℕ) : PronicHilbertSpace :=
  pronicPositiveCoordinates (pronicFiniteCoordinates v N)

/-- The finite extension retains every prescribed positive source coordinate. -/
theorem pronicFiniteExtension_coordinate (v : ℕ → ℂ) {N n : ℕ}
    (hn0 : 0 < n) (hnN : n ≤ N) :
    pronicRowCoordinate n (pronicFiniteExtension v N) = v n := by
  have hnroot : (pronicCoordinateRoot n : ℂ) ≠ 0 := by
    exact_mod_cast (pronicCoordinateRoot_pos hn0).ne'
  rw [pronicRowCoordinate_apply, PNatBlock.extZero, dif_pos hn0]
  change (pronicCoordinateRoot n : ℂ) *
    (if n - 1 < N then v (n - 1 + 1) / (pronicCoordinateRoot (n - 1 + 1) : ℂ) else 0) = v n
  rw [if_pos (by omega : n - 1 < N), show n - 1 + 1 = n by omega]
  field_simp [hnroot]

/-- The formal finite cofactor action of an actual Wiener kernel. -/
def formalWienerCofactor (a : WienerAlgebraAt (1 / 2)) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, a.toFn j * v (n / j)

/-- Every coordinate within the prescribed horizon agrees with the formal source action. -/
theorem pronicFiniteExtension_wiener (a : WienerAlgebraAt (1 / 2))
    (v : ℕ → ℂ) (N n : ℕ) (hnN : n ≤ N) :
    pronicRowCoordinate n (pronicWienerRepresentation a (pronicFiniteExtension v N)) =
      formalWienerCofactor a v n := by
  rw [pronicRowCoordinate_wiener, formalWienerCofactor]
  apply sum_congr rfl
  intro j hj
  have hjn := mem_Icc.mp hj
  rw [pronicFiniteExtension_coordinate v
    ((Nat.one_le_div_iff hjn.1).mpr hjn.2) ((Nat.div_le_self n j).trans hnN)]

/-- Formal cofactor actions compose for every source row; no infinite-energy assumption is needed. -/
theorem formalWienerCofactor_comp (a b : WienerAlgebraAt (1 / 2))
    (v : ℕ → ℂ) (n : ℕ) :
    formalWienerCofactor a (formalWienerCofactor b v) n =
      formalWienerCofactor (a * b) v n := by
  let f := pronicFiniteExtension v n
  calc
    _ = ∑ j ∈ Icc 1 n, a.toFn j *
        pronicRowCoordinate (n / j) (pronicWienerRepresentation b f) := by
      apply sum_congr rfl
      intro j _
      rw [pronicFiniteExtension_wiener b v n (n / j) (Nat.div_le_self n j)]
    _ = pronicRowCoordinate n
        (pronicWienerRepresentation a (pronicWienerRepresentation b f)) :=
      (pronicRowCoordinate_wiener a (pronicWienerRepresentation b f) n).symm
    _ = pronicRowCoordinate n (pronicWienerRepresentation (a * b) f) := by
      rw [map_mul]
      rfl
    _ = _ := pronicFiniteExtension_wiener (a * b) v n n le_rfl

end GaloisForLFunctions.BiarithmeticGeometry

