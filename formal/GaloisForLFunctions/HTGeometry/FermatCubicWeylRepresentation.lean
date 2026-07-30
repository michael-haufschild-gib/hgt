import GaloisForLFunctions.HTGeometry.FermatCubicCliffordHorizon
import GaloisForLFunctions.HTGeometry.GeneralizedCliffordPrincipalSymbolFaithfulness
import Mathlib.Tactic.Ring

/-!
# The three-state Weyl representation of the Fermat cubic horizon

The order-three clock, shift, and a third Weyl monomial give an explicit three-dimensional
representation of the Fermat cubic generalized Clifford relations.  Combined with the abstract
shift-suspension theorem, this removes the representation hypothesis from the cubic horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The order-three clock operator. -/
def fermatCubicClock (ω : K) : Module.End K (Fin 3 → K) where
  toFun f i := ![1, ω, ω ^ 2] i * f i
  map_add' f g := by
    funext i
    simp [mul_add]
  map_smul' c f := by
    funext i
    simp [mul_assoc, mul_comm]

/-- The cyclic order-three shift. -/
def fermatCubicShift : Module.End K (Fin 3 → K) where
  toFun f := ![f 2, f 0, f 1]
  map_add' f g := by
    funext i
    fin_cases i <;> simp
  map_smul' c f := by
    funext i
    fin_cases i <;> simp

/-- The third Weyl generator `clock²·shift`, written coordinatewise. -/
def fermatCubicThird (ω : K) : Module.End K (Fin 3 → K) where
  toFun f := ![f 2, ω ^ 2 * f 0, ω * f 1]
  map_add' f g := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' c f := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The cubic cyclotomic relation implies `ω³=1`. -/
theorem cube_eq_one_of_sq_add_self_add_one_eq_zero
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  calc
    ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
    _ = 1 := by rw [hω]; ring

theorem cube_nested_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω * (ω * (ω * x)) = x := by
  calc
    ω * (ω * (ω * x)) = ω ^ 3 * x := by ring
    _ = x := by rw [hω3, one_mul]

theorem sixth_nested_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω * (ω * (ω * (ω * (ω * (ω * x))))) = x := by
  calc
    ω * (ω * (ω * (ω * (ω * (ω * x))))) = (ω ^ 3) ^ 2 * x := by ring
    _ = x := by rw [hω3, one_pow, one_mul]

theorem cube_square_nested_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω ^ 2 * (ω ^ 2 * (ω ^ 2 * x)) = x := by
  calc
    ω ^ 2 * (ω ^ 2 * (ω ^ 2 * x)) = (ω ^ 3) ^ 2 * x := by ring
    _ = x := by rw [hω3, one_pow, one_mul]

theorem omega_mul_square_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω * (ω ^ 2 * x) = x := by
  calc
    ω * (ω ^ 2 * x) = ω ^ 3 * x := by ring
    _ = x := by rw [hω3, one_mul]

theorem square_mul_omega_mul_eq
    (ω x : K) (hω3 : ω ^ 3 = 1) :
    ω ^ 2 * (ω * x) = x := by
  calc
    ω ^ 2 * (ω * x) = ω ^ 3 * x := by ring
    _ = x := by rw [hω3, one_mul]

theorem fermatCubicClock_cube
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicClock ω ^ 3 = 1 := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicClock, Module.End.pow_apply,
      Function.iterate_succ_apply', cube_nested_mul_eq ω _ hω3,
      cube_square_nested_mul_eq ω _ hω3]

theorem fermatCubicShift_cube :
    (fermatCubicShift (K := K)) ^ 3 = 1 := by
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicShift, Module.End.pow_apply, Function.iterate_succ_apply']

theorem fermatCubicThird_cube
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicThird ω ^ 3 = 1 := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicThird, Module.End.pow_apply,
      Function.iterate_succ_apply', omega_mul_square_mul_eq ω _ hω3,
      square_mul_omega_mul_eq ω _ hω3]

theorem fermatCubicClock_mul_shift
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicClock ω * fermatCubicShift =
      ω • (fermatCubicShift * fermatCubicClock ω) := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicClock, fermatCubicShift, Module.End.mul_apply,
      cube_nested_mul_eq ω _ hω3, pow_two, mul_assoc]

theorem fermatCubicClock_mul_third
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicClock ω * fermatCubicThird ω =
      ω • (fermatCubicThird ω * fermatCubicClock ω) := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicClock, fermatCubicThird, Module.End.mul_apply,
      cube_nested_mul_eq ω _ hω3, pow_two, mul_assoc]

theorem fermatCubicShift_mul_third
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicShift * fermatCubicThird ω =
      ω • (fermatCubicThird ω * fermatCubicShift) := by
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  apply LinearMap.ext
  intro f
  funext i
  fin_cases i <;>
    simp [fermatCubicShift, fermatCubicThird, Module.End.mul_apply,
      cube_nested_mul_eq ω _ hω3, pow_two, mul_assoc]

/-- A fixed nonzero root state for the three-state Weyl realization. -/
def fermatCubicWeylRoot : Fin 3 → K := ![1, 0, 0]

theorem fermatCubicWeylRoot_ne_zero :
    (fermatCubicWeylRoot (K := K)) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [fermatCubicWeylRoot] at h0

/-- **Explicit Fermat cubic differential-field horizon.**  The three-state Weyl packet has
complete differential dependence exactly on `c₀³+c₁³+c₂³=0`. -/
theorem fermatCubicWeylField_dependenceHorizon_eq
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    {c : Fin 3 → K | ¬ AlgebraicIndependent K
      (generalizedCliffordShiftFieldJet
        (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
          (fermatCubicThird ω) c)
        fermatCubicWeylRoot)} =
      {c : Fin 3 → K | fermatCubicPotential c = 0} := by
  apply fermatCubicShiftField_dependenceHorizon_eq
    ω (fermatCubicClock ω) fermatCubicShift (fermatCubicThird ω)
    hω
    (fermatCubicClock_cube ω hω)
    fermatCubicShift_cube
    (fermatCubicThird_cube ω hω)
    (fermatCubicClock_mul_shift ω hω)
    (fermatCubicClock_mul_third ω hω)
    (fermatCubicShift_mul_third ω hω)
    fermatCubicWeylRoot fermatCubicWeylRoot_ne_zero

/-- The explicit Weyl model also gives a genuine linear law space of rational-field derivations
with the Fermat cubic as its exact dependence horizon. -/
theorem fermatCubicWeylLinearDependenceHorizon_eq
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    linearDerivationDependenceHorizon
        (generalizedCliffordShiftFieldDerivationLaw
          (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
            (fermatCubicThird ω)))
        (generalizedCliffordShiftFieldRoot fermatCubicWeylRoot) =
      {c : Fin 3 → K | fermatCubicPotential c = 0} := by
  apply fermatCubicLinearDependenceHorizon_eq
    ω (fermatCubicClock ω) fermatCubicShift (fermatCubicThird ω)
    hω
    (fermatCubicClock_cube ω hω)
    fermatCubicShift_cube
    (fermatCubicThird_cube ω hω)
    (fermatCubicClock_mul_shift ω hω)
    (fermatCubicClock_mul_third ω hω)
    (fermatCubicShift_mul_third ω hω)
    fermatCubicWeylRoot fermatCubicWeylRoot_ne_zero

/-- A matrix coefficient of an endomorphism in the canonical three-state basis. -/
def fermatCubicEndomorphismCoefficient (i j : Fin 3) :
    Module.End K (Fin 3 → K) →ₗ[K] K where
  toFun T := T (Pi.basisFun K (Fin 3) j) i
  map_add' T U := by simp
  map_smul' c T := by simp

@[simp]
theorem fermatCubicEndomorphismCoefficient_apply
    (i j : Fin 3) (T : Module.End K (Fin 3 → K)) :
    fermatCubicEndomorphismCoefficient i j T =
      T (Pi.basisFun K (Fin 3) j) i := rfl

/-- A canonical coordinate bivector of the ternary law space. -/
def fermatCubicBasisWedge (i j : Fin 3) :
    ⋀[K]^2 (Fin 3 → K) :=
  exteriorPower.ιMulti K 2
    ![Pi.basisFun K (Fin 3) i, Pi.basisFun K (Fin 3) j]

/-- A left-inverse candidate for the internal Weyl commutator symbol.  Its three coefficient
readouts were chosen to separate the three Weyl monomials `[X,Y]`, `[X,Z]`, and `[Y,Z]`. -/
def fermatCubicWeylCommutatorDecoder (ω : K) :
    Module.End K (Fin 3 → K) →ₗ[K] ⋀[K]^2 (Fin 3 → K) :=
  LinearMap.smulRight
      (((ω - 1) ^ 2)⁻¹ •
        (fermatCubicEndomorphismCoefficient (K := K) 2 1 -
          fermatCubicEndomorphismCoefficient (K := K) 1 0))
      (fermatCubicBasisWedge (K := K) 0 1) +
    LinearMap.smulRight
      ((3 : K)⁻¹ •
        (fermatCubicEndomorphismCoefficient (K := K) 2 1 -
          ω • fermatCubicEndomorphismCoefficient (K := K) 1 0))
      (fermatCubicBasisWedge (K := K) 0 2) +
    LinearMap.smulRight
      ((ω ^ 2 - ω)⁻¹ • fermatCubicEndomorphismCoefficient (K := K) 2 0)
      (fermatCubicBasisWedge (K := K) 1 2)

theorem omega_ne_one_of_sq_add_self_add_one_eq_zero
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ 1 := by
  intro h
  rw [h] at hω
  norm_num at hω

theorem omega_sq_ne_one_of_sq_add_self_add_one_eq_zero
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 ≠ 1 := by
  intro hω2
  have hω1 := omega_ne_one_of_sq_add_self_add_one_eq_zero ω hω
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  exact hω1 (by
    calc
      ω = ω ^ 2 * ω := by rw [hω2, one_mul]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3)

theorem omega_ne_zero_of_sq_add_self_add_one_eq_zero
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ 0 := by
  intro h
  rw [h] at hω
  norm_num at hω

@[simp]
theorem fermatCubicWeylCommutatorDecoder_clock_shift
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicWeylCommutatorDecoder ω
        ⁅fermatCubicClock ω, fermatCubicShift⁆ =
      fermatCubicBasisWedge (K := K) 0 1 := by
  have hω1 := omega_ne_one_of_sq_add_self_add_one_eq_zero ω hω
  have hA : (ω - 1) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hω1)
  have hAexp : 1 - ω * 2 + ω ^ 2 ≠ 0 := by
    rw [show 1 - ω * 2 + ω ^ 2 = (ω - 1) ^ 2 by ring]
    exact hA
  have hsub : -1 + ω ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr hω1 : ω - 1 ≠ 0)
  have hthree : (3 : K) ≠ 0 := by norm_num
  simp [fermatCubicWeylCommutatorDecoder, fermatCubicEndomorphismCoefficient,
    fermatCubicClock, fermatCubicShift, LieRing.of_associative_ring_bracket,
    Module.End.mul_apply]
  match_scalars
  all_goals ring_nf
  all_goals field_simp [hA, hAexp, hsub, hthree]
  all_goals ring

@[simp]
theorem fermatCubicWeylCommutatorDecoder_clock_third
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicWeylCommutatorDecoder ω
        ⁅fermatCubicClock ω, fermatCubicThird ω⁆ =
      fermatCubicBasisWedge (K := K) 0 2 := by
  have hω1 := omega_ne_one_of_sq_add_self_add_one_eq_zero ω hω
  have hA : (ω - 1) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hω1)
  have hsub : -1 + ω ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr hω1 : ω - 1 ≠ 0)
  have hω3 := cube_eq_one_of_sq_add_self_add_one_eq_zero ω hω
  have hω4 : ω ^ 4 = ω := by rw [pow_succ, hω3, one_mul]
  have hthree : (3 : K) ≠ 0 := by norm_num
  simp [fermatCubicWeylCommutatorDecoder, fermatCubicEndomorphismCoefficient,
    fermatCubicClock, fermatCubicThird, LieRing.of_associative_ring_bracket,
    Module.End.mul_apply]
  match_scalars
  all_goals ring_nf
  all_goals try field_simp [hA, hsub, hthree]
  all_goals try ring_nf
  all_goals rw [hω3, hω4]
  all_goals linear_combination -hω

@[simp]
theorem fermatCubicWeylCommutatorDecoder_shift_third
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicWeylCommutatorDecoder ω
        ⁅fermatCubicShift (K := K), fermatCubicThird ω⁆ =
      fermatCubicBasisWedge (K := K) 1 2 := by
  have hω1 := omega_ne_one_of_sq_add_self_add_one_eq_zero ω hω
  have hω0 := omega_ne_zero_of_sq_add_self_add_one_eq_zero ω hω
  have hC : -ω + ω ^ 2 ≠ 0 := by
    rw [show -ω + ω ^ 2 = ω * (ω - 1) by ring]
    exact mul_ne_zero hω0 (sub_ne_zero.mpr hω1)
  have hA : (ω - 1) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hω1)
  have hsub : -1 + ω ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr hω1 : ω - 1 ≠ 0)
  have hthree : (3 : K) ≠ 0 := by norm_num
  simp [fermatCubicWeylCommutatorDecoder, fermatCubicEndomorphismCoefficient,
    fermatCubicShift, fermatCubicThird, LieRing.of_associative_ring_bracket,
    Module.End.mul_apply]
  match_scalars
  all_goals ring_nf
  all_goals field_simp [hA, hsub, hC, hthree]

/-- Reversing the canonical law directions reverses the coordinate bivector. -/
theorem fermatCubicBasisWedge_swap (i j : Fin 3) :
    fermatCubicBasisWedge (K := K) j i =
      -fermatCubicBasisWedge (K := K) i j := by
  simpa [fermatCubicBasisWedge, Function.comp_def] using!
    (exteriorPower.ιMulti K 2).map_swap
      (![Pi.basisFun K (Fin 3) i, Pi.basisFun K (Fin 3) j]) Fin.zero_ne_one

theorem fermatCubicWeylCommutatorDecoder_swap
    (A B : Module.End K (Fin 3 → K)) (ω : K) :
    fermatCubicWeylCommutatorDecoder ω ⁅B, A⁆ =
      -fermatCubicWeylCommutatorDecoder ω ⁅A, B⁆ := by
  have hcomm : ⁅B, A⁆ = -⁅A, B⁆ := by
    simp [LieRing.of_associative_ring_bracket]
  rw [hcomm, map_neg]

@[simp]
theorem fermatCubicWeylCommutatorDecoder_shift_clock
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicWeylCommutatorDecoder ω
        ⁅fermatCubicShift (K := K), fermatCubicClock ω⁆ =
      fermatCubicBasisWedge (K := K) 1 0 := by
  rw [fermatCubicWeylCommutatorDecoder_swap,
    fermatCubicWeylCommutatorDecoder_clock_shift ω hω,
    fermatCubicBasisWedge_swap]
  simp

@[simp]
theorem fermatCubicWeylCommutatorDecoder_third_clock
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicWeylCommutatorDecoder ω
        ⁅fermatCubicThird ω, fermatCubicClock ω⁆ =
      fermatCubicBasisWedge (K := K) 2 0 := by
  rw [fermatCubicWeylCommutatorDecoder_swap,
    fermatCubicWeylCommutatorDecoder_clock_third ω hω,
    fermatCubicBasisWedge_swap]
  simp

@[simp]
theorem fermatCubicWeylCommutatorDecoder_third_shift
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    fermatCubicWeylCommutatorDecoder ω
        ⁅fermatCubicThird ω, fermatCubicShift (K := K)⁆ =
      fermatCubicBasisWedge (K := K) 2 1 := by
  rw [fermatCubicWeylCommutatorDecoder_swap,
    fermatCubicWeylCommutatorDecoder_shift_third ω hω,
    fermatCubicBasisWedge_swap]
  simp

/-- The explicit three-state decoder is a left inverse to the full internal commutator symbol. -/
theorem fermatCubicWeylCommutatorDecoder_comp_eq_id
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (fermatCubicWeylCommutatorDecoder ω).comp
        (endomorphismCommutatorMap
          (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
            (fermatCubicThird ω))) =
      LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply (Pi.basisFun K (Fin 3)).ext_alternating
  intro f hf
  change fermatCubicWeylCommutatorDecoder ω
      (endomorphismCommutatorMap
        (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
          (fermatCubicThird ω))
        (exteriorPower.ιMulti K 2
          ![Pi.basisFun K (Fin 3) (f 0), Pi.basisFun K (Fin 3) (f 1)])) = _
  rw [endomorphismCommutatorMap_wedge, fermatCubicSymbol_apply]
  generalize h0 : f 0 = i
  generalize h1 : f 1 = j
  have hvec : (fun r : Fin 2 ↦ Pi.basisFun K (Fin 3) (f r)) =
      ![Pi.basisFun K (Fin 3) i, Pi.basisFun K (Fin 3) j] := by
    funext r
    fin_cases r
    · simpa using congrArg (Pi.basisFun K (Fin 3)) h0
    · simpa using congrArg (Pi.basisFun K (Fin 3)) h1
  rw [hvec]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (Fin.zero_ne_one (hf (h0.trans h1.symm))).elim
    | simpa [fermatCubicBasisWedge] using
        (fermatCubicWeylCommutatorDecoder_clock_shift ω hω)
    | simpa [fermatCubicBasisWedge] using
        (fermatCubicWeylCommutatorDecoder_clock_third ω hω)
    | simpa [fermatCubicBasisWedge] using
        (fermatCubicWeylCommutatorDecoder_shift_clock ω hω)
    | simpa [fermatCubicBasisWedge] using
        (fermatCubicWeylCommutatorDecoder_shift_third ω hω)
    | simpa [fermatCubicBasisWedge] using
        (fermatCubicWeylCommutatorDecoder_third_clock ω hω)
    | simpa [fermatCubicBasisWedge] using
        (fermatCubicWeylCommutatorDecoder_third_shift ω hω)

/-- The Fermat cubic Weyl principal symbol has maximal possible bivector rank. -/
theorem fermatCubicWeyl_endomorphismCommutatorMap_injective
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
          (fermatCubicThird ω))) := by
  intro z z' hzz'
  have hdecoded := congrArg (fermatCubicWeylCommutatorDecoder ω) hzz'
  have hleft := LinearMap.congr_fun
    (fermatCubicWeylCommutatorDecoder_comp_eq_id ω hω)
  calc
    z = fermatCubicWeylCommutatorDecoder ω
        (endomorphismCommutatorMap
          (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
            (fermatCubicThird ω)) z) := (hleft z).symm
    _ = fermatCubicWeylCommutatorDecoder ω
        (endomorphismCommutatorMap
          (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
            (fermatCubicThird ω)) z') := hdecoded
    _ = z' := hleft z'

/-- **Maximal Fermat-cubic hypertranscendence horizon.**  The explicit Weyl packet has the Fermat
cubic as its exact scalar dependence horizon and preserves every nonzero bivector as a nonzero
differential-field commutator. -/
theorem fermatCubicWeyl_maximalHorizon
    [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    linearDerivationDependenceHorizon
        (generalizedCliffordShiftFieldDerivationLaw
          (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
            (fermatCubicThird ω)))
        (generalizedCliffordShiftFieldRoot fermatCubicWeylRoot) =
        {c : Fin 3 → K | fermatCubicPotential c = 0} ∧
      Function.Injective
        (derivationCommutatorMap
          (generalizedCliffordShiftFieldDerivationLaw
            (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
              (fermatCubicThird ω)))) := by
  refine ⟨fermatCubicWeylLinearDependenceHorizon_eq ω hω, ?_⟩
  exact (generalizedCliffordField_derivationCommutatorMap_injective_iff
    (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
      (fermatCubicThird ω))).2
    (fermatCubicWeyl_endomorphismCommutatorMap_injective ω hω)

end

end GaloisForLFunctions.HTGeometry
