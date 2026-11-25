import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.BoundaryError

/-! # Physical propagators under selective dilation of the path disorder -/

open Finset Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
open LocalPatches
noncomputable section
variable {n : ℕ}

/-- Retain precisely the chosen coupling coordinates. -/
def restrictShell (S : Finset (PathLabel n)) (u : PathShell n) : PathShell n :=
  WithLp.toLp 2 fun l => if l∈S then u l else 0

/-- Increase the selected physical couplings by a common fraction. -/
def dilateShell (S : Finset (PathLabel n)) (a : ℝ) (u : PathShell n) : PathShell n :=
  u+a • restrictShell S u

private theorem skew_sum (u : PathShell n) :
    (-Complex.I) • pathHamiltonian u=∑ l, pathTermGenerator u l := by
  rw [pathHamiltonian_eq_sum,Finset.smul_sum]
  rfl

private theorem skew_restrict (S : Finset (PathLabel n)) (u : PathShell n) :
    (-Complex.I) • pathHamiltonian (restrictShell S u)=∑ l ∈ S, pathTermGenerator u l := by
  rw [skew_sum]
  have hs : univ.filter (fun l => l∈S)=S := by ext; simp
  have he : (∑ l : PathLabel n, if l∈S then pathTermGenerator u l else 0)=
      ∑ l ∈ S, pathTermGenerator u l := by rw [←Finset.sum_filter,hs]
  rw [←he]
  apply sum_congr rfl
  intro l _
  by_cases hl : l∈S <;> simp [restrictShell,pathTermGenerator,hl]

private theorem term_dilate (S : Finset (PathLabel n)) (a : ℝ) (u : PathShell n) (l : PathLabel n) :
    pathTermGenerator (dilateShell S a u) l =
      a • pathTermGenerator (restrictShell S u) l + pathTermGenerator u l := by
  let P := finitePauliMatrix (pathWord l)
  let v := restrictShell S u
  change (-Complex.I) • ((((u l+a*v l:ℝ):ℂ)) • P)=
    a • ((-Complex.I) • ((v l:ℂ) • P)) + (-Complex.I) • ((u l:ℂ) • P)
  rw [Complex.ofReal_add,Complex.ofReal_mul,add_smul,smul_add,add_comm,mul_smul]
  congr 1
  rw [smul_comm (-Complex.I),Complex.coe_smul]

/-- At every nonnegative time, the physical selective dilation is
approximated by a local rotation before the original evolution with
error controlled by the interaction mass at the selected boundary. -/
theorem physical_rotation_error (u : PathShell n) (S : Finset (PathLabel n))
    {a t : ℝ} (ha : 0≤a) (ht : 0≤t) :
    ‖unitaryEvolution (pathHamiltonian (dilateShell S a u)) t -
      unitaryEvolution (pathHamiltonian (restrictShell S u)) (t*a)*
        unitaryEvolution (pathHamiltonian u) t‖ ≤ t^2*a*boundaryMass u S := by
  have hsum : (-Complex.I) • pathHamiltonian (dilateShell S a u)=
      a • (∑ l ∈ S, pathTermGenerator u l)+(∑ l, pathTermGenerator u l) := by
    rw [skew_sum]
    simp_rw [term_dilate S a u]
    rw [sum_add_distrib,←Finset.smul_sum,←skew_sum,skew_restrict]
  unfold unitaryEvolution
  rw [hsum,skew_restrict,skew_sum]
  exact subset_dilation_error u S ht ha

#print axioms physical_rotation_error
end
end GaloisForLFunctions.HTGeometry.BlockDilations
