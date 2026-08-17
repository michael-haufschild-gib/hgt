import GaloisForLFunctions.RHTower.ArchimedeanAxisMode
import GaloisForLFunctions.HTGeometry.BohrGenerators
import GaloisForLFunctions.HTGeometry.GammaLogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra

noncomputable section

/-- Finite integer Fourier modes on the prime lanes. -/
abbrev PrimeMode : Type := Nat.Primes →₀ ℤ

/-- The Bohr Fourier algebra: finite `ℂ`-combinations of the modes `e_m`, with the ring product
`e_m · e_{m'} = e_{m+m'}`. -/
abbrev BohrAlgebra : Type := AddMonoidAlgebra ℂ PrimeMode

/-- The mode `e_m`. -/
def mode (m : PrimeMode) : BohrAlgebra := AddMonoidAlgebra.single m 1

/-- **The ring product adds modes.** -/
theorem mode_mul (m m' : PrimeMode) : mode m * mode m' = mode (m + m') := by
  rw [mode, mode, mode, AddMonoidAlgebra.single_mul_single, one_mul]

/-- A diagonal Fourier operator: it multiplies the coefficient of each mode by a scalar depending
only on that mode. -/
def diagOp (c : PrimeMode → ℂ) : BohrAlgebra →ₗ[ℂ] BohrAlgebra :=
  (AddMonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    (Finsupp.lsum ℂ (fun m => c m • (Finsupp.lsingle m : ℂ →ₗ[ℂ] (PrimeMode →₀ ℂ)))) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem diagOp_single (c : PrimeMode → ℂ) (m : PrimeMode) (z : ℂ) :
    diagOp c (AddMonoidAlgebra.single m z) = AddMonoidAlgebra.single m (c m * z) := by
  have h1 : (AddMonoidAlgebra.coeffLinearEquiv ℂ) (AddMonoidAlgebra.single m z)
      = Finsupp.single m z := rfl
  rw [diagOp]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1,
    Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single,
    smul_eq_mul]
  rfl

@[simp] theorem diagOp_mode (c : PrimeMode → ℂ) (m : PrimeMode) :
    diagOp c (mode m) = c m • mode m := by
  rw [mode, diagOp_single, mul_one, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

end

end GaloisForLFunctions.BohrGeneratorAxis

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra

noncomputable section

/-- **A diagonal operator acts coefficientwise.** -/
theorem coeff_diagOp (c : PrimeMode → ℂ) (a : BohrAlgebra) (m : PrimeMode) :
    (diagOp c a).coeff m = c m * a.coeff m := by
  classical
  have key : ∀ f : PrimeMode →₀ ℂ,
      (diagOp c (AddMonoidAlgebra.ofCoeff f)).coeff m = c m * f m := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
        have h : (AddMonoidAlgebra.ofCoeff (f + g) : BohrAlgebra)
            = AddMonoidAlgebra.ofCoeff f + AddMonoidAlgebra.ofCoeff g := rfl
        rw [h, map_add]
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg]
        ring
    | single b z =>
        have h : (AddMonoidAlgebra.ofCoeff (Finsupp.single b z) : BohrAlgebra)
            = AddMonoidAlgebra.single b z := rfl
        rw [h, diagOp_single]
        rcases eq_or_ne b m with rfl | hbm
        · simp [AddMonoidAlgebra.coeff_single]
        · simp [AddMonoidAlgebra.coeff_single, hbm]
  exact key a.coeff

/-- **Diagonal operators preserve Fourier support.**  This is the whole content of "a diagonal
operator cannot manufacture a new mode". -/
theorem diagOp_mem_supported {c : PrimeMode → ℂ} {a : BohrAlgebra} {S : Set PrimeMode}
    (h : a ∈ AddMonoidAlgebra.supported ℂ ℂ S) :
    diagOp c a ∈ AddMonoidAlgebra.supported ℂ ℂ S := by
  rw [AddMonoidAlgebra.mem_supported'] at h ⊢
  intro m hm
  rw [coeff_diagOp, h m hm, mul_zero]

theorem diagOp_comp (c d : PrimeMode → ℂ) :
    (diagOp c) ∘ₗ (diagOp d) = diagOp (fun m => c m * d m) := by
  refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  simp [coeff_diagOp, mul_assoc]

theorem diagOp_add (c d : PrimeMode → ℂ) :
    diagOp (c + d) = diagOp c + diagOp d := by
  refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  simp [coeff_diagOp, add_mul]

theorem diagOp_one : diagOp 1 = LinearMap.id := by
  refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  simp [coeff_diagOp]

theorem diagOp_smul (z : ℂ) (c : PrimeMode → ℂ) :
    diagOp (z • c) = z • diagOp c := by
  refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  simp [coeff_diagOp, mul_assoc]

/-- The algebra of diagonal Fourier operators, as the image of the pointwise-multiplier algebra. -/
def diagAlgHom : (PrimeMode → ℂ) →ₐ[ℂ] Module.End ℂ BohrAlgebra where
  toFun := diagOp
  map_one' := diagOp_one
  map_mul' c d := by
    refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
    simp [coeff_diagOp, mul_assoc]
  map_zero' := by
    refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
    simp [coeff_diagOp]
  map_add' := diagOp_add
  commutes' z := by
    refine LinearMap.ext fun a => AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
    simp [coeff_diagOp, Algebra.algebraMap_eq_smul_one]

@[simp] theorem diagAlgHom_apply (c : PrimeMode → ℂ) : diagAlgHom c = diagOp c := rfl

end

end GaloisForLFunctions.BohrGeneratorAxis

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra

noncomputable section

/-! ## The two generators -/

/-- The prime dilation multiplier `p^{-m_p}`. -/
def sigmaMult (p : Nat.Primes) (m : PrimeMode) : ℂ := ((p : ℕ) : ℂ) ^ (-(m p))

/-- The single-lane Euler operator multiplier `m_p`. -/
def thetaMult (p : Nat.Primes) (m : PrimeMode) : ℂ := ((m p : ℤ) : ℂ)

/-- The archimedean generator multiplier `-(m · ℓ)`. -/
def dsMult (m : PrimeMode) : ℂ := -primeLogFrequencyComplex m

/-- The prime dilation `σ_p`. -/
def sigmaOp (p : Nat.Primes) : Module.End ℂ BohrAlgebra := diagOp (sigmaMult p)

/-- The single-lane Euler operator `θ_p = x_p ∂_{x_p}`. -/
def thetaOp (p : Nat.Primes) : Module.End ℂ BohrAlgebra := diagOp (thetaMult p)

/-- The archimedean generator `∂_s`. -/
def dsOp : Module.End ℂ BohrAlgebra := diagOp dsMult

/-- **`σ_p` is Fourier-diagonal:** `σ_p e_m = p^{-m_p} e_m`. -/
theorem sigmaOp_mode (p : Nat.Primes) (m : PrimeMode) :
    sigmaOp p (mode m) = (((p : ℕ) : ℂ) ^ (-(m p))) • mode m := diagOp_mode _ _

/-- **`θ_p` is Fourier-diagonal:** `θ_p e_m = m_p e_m`. -/
theorem thetaOp_mode (p : Nat.Primes) (m : PrimeMode) :
    thetaOp p (mode m) = ((m p : ℤ) : ℂ) • mode m := diagOp_mode _ _

/-- **`∂_s` is Fourier-diagonal:** `∂_s e_m = -(m · ℓ) e_m`. -/
theorem dsOp_mode (m : PrimeMode) :
    dsOp (mode m) = (-primeLogFrequencyComplex m) • mode m := diagOp_mode _ _

/-- **`∂_s = -Σ_p (log p) θ_p` on every mode.**  The sum is finite because the mode has finite
support: the infinite prime sum never leaves the lanes already occupied by `m`. -/
theorem dsMult_eq_neg_sum (m : PrimeMode) :
    dsMult m = -∑ p ∈ m.support, (Real.log (p : ℕ) : ℂ) * thetaMult p m := by
  rw [dsMult, primeLogFrequencyComplex, Finsupp.sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thetaMult]
  ring

theorem dsOp_mode_eq_neg_sum (m : PrimeMode) :
    dsOp (mode m) = -∑ p ∈ m.support, (Real.log (p : ℕ) : ℂ) • thetaOp p (mode m) := by
  rw [dsOp, diagOp_mode, dsMult_eq_neg_sum m, neg_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thetaOp_mode, smul_smul, thetaMult]

/-- **Flat curvature at the generator level:** all diagonal operators commute, in particular
`[∂_s, σ_p] = 0` and `[θ_p, θ_q] = 0`. -/
theorem diagOp_commute (c d : PrimeMode → ℂ) : diagOp c * diagOp d = diagOp d * diagOp c := by
  rw [← diagAlgHom_apply, ← diagAlgHom_apply, ← map_mul, ← map_mul, mul_comm]

theorem sigmaOp_dsOp_commute (p : Nat.Primes) : sigmaOp p * dsOp = dsOp * sigmaOp p :=
  diagOp_commute _ _

theorem thetaOp_commute (p q : Nat.Primes) : thetaOp p * thetaOp q = thetaOp q * thetaOp p :=
  diagOp_commute _ _

theorem sigmaOp_thetaOp_commute (p q : Nat.Primes) :
    sigmaOp p * thetaOp q = thetaOp q * sigmaOp p := diagOp_commute _ _

/-! ## Axis modes versus combination modes -/

/-- The axis modes: supported on at most one prime lane. -/
def axisSet : Set PrimeMode := {m | m.support.card ≤ 1}

/-- A combination mode occupies at least two prime lanes. -/
def IsCombinationMode (m : PrimeMode) : Prop := 2 ≤ m.support.card

theorem not_mem_axisSet_of_isCombinationMode {m : PrimeMode} (hm : IsCombinationMode m) :
    m ∉ axisSet := by
  intro h
  exact absurd (le_trans hm h) (by norm_num)

/-- The submodule of axis-mode elements. -/
def axisSupported : Submodule ℂ BohrAlgebra := AddMonoidAlgebra.supported ℂ ℂ axisSet

theorem mode_mem_axisSupported {m : PrimeMode} (hm : m ∈ axisSet) : mode m ∈ axisSupported := by
  rw [axisSupported, AddMonoidAlgebra.mem_supported']
  intro n hn
  rw [mode, AddMonoidAlgebra.coeff_single]
  refine Finsupp.single_eq_of_ne ?_
  rintro rfl
  exact hn hm

theorem mode_not_mem_axisSupported {m : PrimeMode} (hm : IsCombinationMode m) :
    mode m ∉ axisSupported := by
  rw [axisSupported, AddMonoidAlgebra.mem_supported']
  intro h
  have h0 := h m (not_mem_axisSet_of_isCombinationMode hm)
  rw [mode, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h0
  exact one_ne_zero h0

end

end GaloisForLFunctions.BohrGeneratorAxis

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra

noncomputable section

/-! ## The generator algebra is diagonal, hence combination-mode free -/

/-- The full generator set of the completed `(σ_p, ∂_s)`-connection, including every single-lane
Euler operator `θ_p`. -/
def generators : Set (Module.End ℂ BohrAlgebra) :=
  (Set.range sigmaOp ∪ Set.range thetaOp) ∪ {dsOp}

/-- The unital `ℂ`-algebra generated by the connection generators. -/
def generatorAlgebra : Subalgebra ℂ (Module.End ℂ BohrAlgebra) := Algebra.adjoin ℂ generators

theorem generators_subset_diagonal :
    generators ⊆ (diagAlgHom : (PrimeMode → ℂ) →ₐ[ℂ] Module.End ℂ BohrAlgebra).range := by
  rintro T ((⟨p, rfl⟩ | ⟨p, rfl⟩) | rfl)
  · exact ⟨sigmaMult p, rfl⟩
  · exact ⟨thetaMult p, rfl⟩
  · exact ⟨dsMult, rfl⟩

/-- **Everything the generators generate is diagonal.** -/
theorem generatorAlgebra_le_diagonal :
    generatorAlgebra ≤ (diagAlgHom : (PrimeMode → ℂ) →ₐ[ℂ] Module.End ℂ BohrAlgebra).range :=
  Algebra.adjoin_le generators_subset_diagonal

/-- **The generator algebra preserves every Fourier support class.** -/
theorem generatorAlgebra_mem_supported {T : Module.End ℂ BohrAlgebra} (hT : T ∈ generatorAlgebra)
    {S : Set PrimeMode} {a : BohrAlgebra} (ha : a ∈ AddMonoidAlgebra.supported ℂ ℂ S) :
    T a ∈ AddMonoidAlgebra.supported ℂ ℂ S := by
  obtain ⟨c, hc⟩ := generatorAlgebra_le_diagonal hT
  rw [← hc]
  exact diagOp_mem_supported ha

/-- **The generator level is combination-mode free.**  No operator built from the prime dilations,
the single-lane Euler operators and the archimedean generator can move an axis-mode element out of
the axis-mode submodule. -/
theorem generatorAlgebra_preserves_axisSupported {T : Module.End ℂ BohrAlgebra}
    (hT : T ∈ generatorAlgebra) {a : BohrAlgebra} (ha : a ∈ axisSupported) :
    T a ∈ axisSupported := generatorAlgebra_mem_supported hT ha

/-- Sharper form: every combination-mode Fourier coefficient of a generator image of an axis-mode
element vanishes. -/
theorem generatorAlgebra_coeff_combinationMode_eq_zero {T : Module.End ℂ BohrAlgebra}
    (hT : T ∈ generatorAlgebra) {a : BohrAlgebra} (ha : a ∈ axisSupported)
    {m : PrimeMode} (hm : IsCombinationMode m) : (T a).coeff m = 0 := by
  have h := generatorAlgebra_preserves_axisSupported hT ha
  rw [axisSupported, AddMonoidAlgebra.mem_supported'] at h
  exact h m (not_mem_axisSet_of_isCombinationMode hm)

/-! ## The ring product does create combination modes -/

theorem support_twoAxis {p q : Nat.Primes} (hpq : p ≠ q) {k l : ℤ} (hk : k ≠ 0) (hl : l ≠ 0) :
    (Finsupp.single p k + Finsupp.single q l).support = {p, q} := by
  classical
  have hdisj : Disjoint (Finsupp.single p k).support (Finsupp.single q l).support := by
    rw [Finsupp.support_single_ne_zero p hk, Finsupp.support_single_ne_zero q hl]
    simp [hpq]
  rw [Finsupp.support_add_eq hdisj, Finsupp.support_single_ne_zero p hk,
    Finsupp.support_single_ne_zero q hl]
  rfl

theorem isCombinationMode_twoAxis {p q : Nat.Primes} (hpq : p ≠ q) {k l : ℤ}
    (hk : k ≠ 0) (hl : l ≠ 0) :
    IsCombinationMode (Finsupp.single p k + Finsupp.single q l) := by
  classical
  rw [IsCombinationMode, support_twoAxis hpq hk hl, Finset.card_insert_of_notMem (by simpa using hpq),
    Finset.card_singleton]

theorem axisSet_single (p : Nat.Primes) (k : ℤ) : (Finsupp.single p k : PrimeMode) ∈ axisSet := by
  classical
  rw [axisSet, Set.mem_setOf_eq]
  exact le_trans (Finset.card_le_card (Finsupp.support_single_subset)) (by simp)

/-- **Combination modes are a ring-product phenomenon.**  Two axis modes on distinct prime lanes lie
in the axis submodule, but their ring product does not. -/
theorem twoAxis_product_not_mem_axisSupported {p q : Nat.Primes} (hpq : p ≠ q) {k l : ℤ}
    (hk : k ≠ 0) (hl : l ≠ 0) :
    mode (Finsupp.single p k) ∈ axisSupported ∧
      mode (Finsupp.single q l) ∈ axisSupported ∧
      mode (Finsupp.single p k) * mode (Finsupp.single q l)
        = mode (Finsupp.single p k + Finsupp.single q l) ∧
      mode (Finsupp.single p k) * mode (Finsupp.single q l) ∉ axisSupported := by
  refine ⟨mode_mem_axisSupported (axisSet_single p k), mode_mem_axisSupported (axisSet_single q l),
    mode_mul _ _, ?_⟩
  rw [mode_mul]
  exact mode_not_mem_axisSupported (isCombinationMode_twoAxis hpq hk hl)

end

end GaloisForLFunctions.BohrGeneratorAxis

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra GaloisForLFunctions

noncomputable section

/-! ## The analytic realization: `∂_s` really is differentiation -/

theorem primeLogFrequencyComplex_zero : primeLogFrequencyComplex (0 : PrimeMode) = 0 := by
  simp [primeLogFrequencyComplex]

theorem primeLogFrequencyComplex_add (m n : PrimeMode) :
    primeLogFrequencyComplex (m + n)
      = primeLogFrequencyComplex m + primeLogFrequencyComplex n := by
  refine Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => ?_)
  push_cast
  ring

theorem archimedeanPrimeMode_zero (s : ℂ) : archimedeanPrimeMode (0 : PrimeMode) s = 1 := by
  rw [archimedeanPrimeMode, primeLogFrequencyComplex_zero]
  simp

theorem archimedeanPrimeMode_add (m n : PrimeMode) (s : ℂ) :
    archimedeanPrimeMode (m + n) s = archimedeanPrimeMode m s * archimedeanPrimeMode n s := by
  rw [archimedeanPrimeMode, archimedeanPrimeMode, archimedeanPrimeMode,
    primeLogFrequencyComplex_add, ← Complex.exp_add]
  ring_nf

/-- The prime modes as a multiplicative family of entire functions. -/
def modeMonoidHom : Multiplicative PrimeMode →* (ℂ → ℂ) where
  toFun m := archimedeanPrimeMode (Multiplicative.toAdd m)
  map_one' := by funext s; exact archimedeanPrimeMode_zero s
  map_mul' m n := by funext s; exact archimedeanPrimeMode_add _ _ s

/-- The analytic realization of the Bohr Fourier algebra as entire functions of `s`. -/
def bohrEval : BohrAlgebra →ₐ[ℂ] (ℂ → ℂ) :=
  AddMonoidAlgebra.lift ℂ (ℂ → ℂ) PrimeMode modeMonoidHom

@[simp] theorem bohrEval_single (m : PrimeMode) (z : ℂ) :
    bohrEval (AddMonoidAlgebra.single m z) = z • archimedeanPrimeMode m := by
  rw [bohrEval, AddMonoidAlgebra.lift_single]
  rfl

@[simp] theorem bohrEval_mode (m : PrimeMode) : bohrEval (mode m) = archimedeanPrimeMode m := by
  rw [mode, bohrEval_single, one_smul]

theorem differentiable_archimedeanPrimeMode (m : PrimeMode) :
    Differentiable ℂ (archimedeanPrimeMode m) := by
  unfold archimedeanPrimeMode
  fun_prop

theorem differentiable_bohrEval (a : BohrAlgebra) : Differentiable ℂ (bohrEval a) := by
  classical
  have key : ∀ f : PrimeMode →₀ ℂ,
      Differentiable ℂ (bohrEval (AddMonoidAlgebra.ofCoeff f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero =>
        have h : (AddMonoidAlgebra.ofCoeff (0 : PrimeMode →₀ ℂ) : BohrAlgebra) = 0 := rfl
        rw [h, map_zero]
        exact differentiable_const 0
    | add f g hf hg =>
        have h : (AddMonoidAlgebra.ofCoeff (f + g) : BohrAlgebra)
            = AddMonoidAlgebra.ofCoeff f + AddMonoidAlgebra.ofCoeff g := rfl
        rw [h, map_add]
        exact hf.add hg
    | single b z =>
        have h : (AddMonoidAlgebra.ofCoeff (Finsupp.single b z) : BohrAlgebra)
            = AddMonoidAlgebra.single b z := rfl
        rw [h, bohrEval_single]
        exact (differentiable_archimedeanPrimeMode b).const_smul z
  exact key a.coeff

/-- **The algebraic archimedean generator is genuine differentiation.**  Under the analytic
realization `e_m ↦ exp(-s (m·ℓ))`, the diagonal operator `∂_s` is `deriv`. -/
theorem deriv_bohrEval (a : BohrAlgebra) : deriv (bohrEval a) = bohrEval (dsOp a) := by
  classical
  have key : ∀ f : PrimeMode →₀ ℂ,
      deriv (bohrEval (AddMonoidAlgebra.ofCoeff f))
        = bohrEval (dsOp (AddMonoidAlgebra.ofCoeff f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero =>
        have h : (AddMonoidAlgebra.ofCoeff (0 : PrimeMode →₀ ℂ) : BohrAlgebra) = 0 := rfl
        rw [h, map_zero, map_zero, map_zero]
        exact deriv_const' 0
    | add f g hf hg =>
        have h : (AddMonoidAlgebra.ofCoeff (f + g) : BohrAlgebra)
            = AddMonoidAlgebra.ofCoeff f + AddMonoidAlgebra.ofCoeff g := rfl
        rw [h, map_add, map_add, map_add, ← hf, ← hg]
        funext s
        exact deriv_add ((differentiable_bohrEval _) s) ((differentiable_bohrEval _) s)
    | single b z =>
        have h : (AddMonoidAlgebra.ofCoeff (Finsupp.single b z) : BohrAlgebra)
            = AddMonoidAlgebra.single b z := rfl
        rw [h, bohrEval_single, dsOp, diagOp_single, bohrEval_single]
        funext s
        have hfun : (z • archimedeanPrimeMode b) = fun t => z * archimedeanPrimeMode b t := rfl
        rw [hfun, deriv_const_mul _ ((differentiable_archimedeanPrimeMode b) s),
          deriv_archimedeanPrimeMode, Pi.smul_apply, smul_eq_mul, dsMult]
        ring
  exact key a.coeff

end

end GaloisForLFunctions.BohrGeneratorAxis

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra GaloisForLFunctions

noncomputable section

/-! ## The infinite prime torus: `σ_p` is precomposition with a coordinate dilation -/

/-- The Bohr characters as a multiplicative family of functions on the infinite prime torus. -/
def torusCharacterHom : Multiplicative PrimeMode →* ((Nat.Primes → ℂˣ) → ℂ) where
  toFun m := fun x => ((bohrCharacter (Multiplicative.toAdd m) x : ℂˣ) : ℂ)
  map_one' := by
    funext x
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) (bohrCharacter_zero (ι := Nat.Primes) x)
  map_mul' m n := by
    funext x
    simpa using congrArg (fun u : ℂˣ => (u : ℂ))
      (bohrCharacter_add (Multiplicative.toAdd m) (Multiplicative.toAdd n) x)

/-- The realization of the Bohr Fourier algebra as functions on the infinite prime torus. -/
def torusEval : BohrAlgebra →ₐ[ℂ] ((Nat.Primes → ℂˣ) → ℂ) :=
  AddMonoidAlgebra.lift ℂ ((Nat.Primes → ℂˣ) → ℂ) PrimeMode torusCharacterHom

@[simp] theorem torusEval_single (m : PrimeMode) (z : ℂ) :
    torusEval (AddMonoidAlgebra.single m z)
      = z • (fun x : Nat.Primes → ℂˣ => ((bohrCharacter m x : ℂˣ) : ℂ)) := by
  rw [torusEval, AddMonoidAlgebra.lift_single]
  rfl

theorem sigmaMult_eq_unit (p : Nat.Primes) (m : PrimeMode) :
    sigmaMult p m = ((((primeComplexUnit p)⁻¹ ^ (m p) : ℂˣ)) : ℂ) := by
  rw [sigmaMult]
  rw [Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  rw [primeComplexUnit]
  simp [zpow_neg]

/-- **The prime dilation is a genuine torus map.**  On the infinite prime torus, the diagonal
operator `σ_p` is precomposition with the coordinate dilation `x_p ↦ p^{-1} x_p`. -/
theorem torusEval_sigmaOp (p : Nat.Primes) (a : BohrAlgebra) (x : Nat.Primes → ℂˣ) :
    torusEval (sigmaOp p a) x
      = torusEval a (scaleCoordinate p (primeComplexUnit p)⁻¹ x) := by
  classical
  have key : ∀ f : PrimeMode →₀ ℂ,
      torusEval (sigmaOp p (AddMonoidAlgebra.ofCoeff f)) x
        = torusEval (AddMonoidAlgebra.ofCoeff f)
            (scaleCoordinate p (primeComplexUnit p)⁻¹ x) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero =>
        have h : (AddMonoidAlgebra.ofCoeff (0 : PrimeMode →₀ ℂ) : BohrAlgebra) = 0 := rfl
        rw [h]
        simp
    | add f g hf hg =>
        have h : (AddMonoidAlgebra.ofCoeff (f + g) : BohrAlgebra)
            = AddMonoidAlgebra.ofCoeff f + AddMonoidAlgebra.ofCoeff g := rfl
        rw [h, map_add, map_add, map_add]
        simp only [Pi.add_apply]
        rw [hf, hg]
    | single b z =>
        have h : (AddMonoidAlgebra.ofCoeff (Finsupp.single b z) : BohrAlgebra)
            = AddMonoidAlgebra.single b z := rfl
        rw [h, sigmaOp, diagOp_single, torusEval_single, torusEval_single]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [bohrCharacter_scaleCoordinate, sigmaMult_eq_unit]
        push_cast
        ring
  exact key a.coeff

/-! ## The archimedean Gamma residue and the rank-one shadow -/

/-- Logarithmic derivative of a real-base complex power along a linear exponent. -/
theorem logDeriv_cpow_linear {c : ℝ} (hc : 0 < c) (a s : ℂ) :
    logDeriv (fun z : ℂ => (c : ℂ) ^ (a * z)) s = a * (Real.log c : ℂ) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hlog : _root_.Complex.log (c : ℂ) = (Real.log c : ℂ) :=
    (_root_.Complex.ofReal_log hc.le).symm
  have hfun : (fun z : ℂ => (c : ℂ) ^ (a * z))
      = fun z : ℂ => _root_.Complex.exp ((Real.log c : ℂ) * a * z) := by
    funext z
    rw [_root_.Complex.cpow_def_of_ne_zero hc0, hlog, mul_assoc]
  have hderiv : HasDerivAt (fun z : ℂ => _root_.Complex.exp ((Real.log c : ℂ) * a * z))
      (_root_.Complex.exp ((Real.log c : ℂ) * a * s) * ((Real.log c : ℂ) * a)) s := by
    have hlin : HasDerivAt (fun z : ℂ => (Real.log c : ℂ) * a * z) ((Real.log c : ℂ) * a) s := by
      simpa using (hasDerivAt_id s).const_mul ((Real.log c : ℂ) * a)
    simpa using hlin.cexp
  have hne := _root_.Complex.exp_ne_zero ((Real.log c : ℂ) * a * s)
  rw [hfun, logDeriv_apply, hderiv.deriv]
  field_simp

/-- **The archimedean Source-A residue.**  The only non-axis content of the archimedean generator is
the digamma of the Gamma factor: `∂_s log Γ_ℝ(s) = -½ log π + ½ ψ(s/2)`. -/
theorem logDeriv_GammaR (s : ℂ) (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv _root_.Complex.Gammaℝ s
      = -(Real.log Real.pi : ℂ) / 2 + _root_.Complex.digamma (s / 2) / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hcpow : ∀ w : ℂ, (Real.pi : ℂ) ^ w ≠ 0 := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (_root_.Complex.cpow_ne_zero_iff_of_exponent_ne_zero hw).mpr hpi0
  have hGne : _root_.Complex.Gamma (s / 2) ≠ 0 := _root_.Complex.Gamma_ne_zero hs
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    have hlin : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s :=
      (differentiableAt_id.neg).div_const 2
    exact DifferentiableAt.const_cpow hlin (Or.inl hpi0)
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => _root_.Complex.Gamma (z / 2)) s := by
    have hlin : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := differentiableAt_id.div_const 2
    exact (_root_.Complex.differentiableAt_Gamma (s / 2) hs).comp s hlin
  have hfun : _root_.Complex.Gammaℝ
      = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * _root_.Complex.Gamma (z / 2) :=
    funext _root_.Complex.Gammaℝ_def
  rw [hfun, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => _root_.Complex.Gamma (z / 2)) s (hcpow (-s / 2)) hGne hd1 hd2]
  have h1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
      = -(Real.log Real.pi : ℂ) / 2 := by
    have hrw : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
        = fun z : ℂ => (Real.pi : ℂ) ^ ((-1 / 2 : ℂ) * z) := by
      funext z; ring_nf
    rw [hrw, logDeriv_cpow_linear hpi]
    ring
  have h2 : logDeriv (fun z : ℂ => _root_.Complex.Gamma (z / 2)) s
      = _root_.Complex.digamma (s / 2) / 2 := by
    have hrw : (fun z : ℂ => _root_.Complex.Gamma (z / 2))
        = fun z : ℂ => _root_.Complex.Gamma ((1 / 2 : ℂ) * z + 0) := by
      funext z; ring_nf
    have hs' : ∀ m : ℕ, (1 / 2 : ℂ) * s + 0 ≠ -(m : ℂ) := by
      intro m
      have := hs m
      intro hcon
      exact this (by rw [← hcon]; ring)
    rw [hrw, HTGeometry.logDeriv_Gamma_affine s hs']
    rw [show (1 / 2 : ℂ) * s + 0 = s / 2 by ring]
    ring
  rw [h1, h2]

/-- **Door-5 rank-one shadow.**  Over a one-lane base every Fourier mode is an axis mode: the
rank-one pro-torus has no combination modes at all. -/
theorem rankOne_no_combination_modes (m : Unit →₀ ℤ) : m.support.card ≤ 1 := by
  classical
  calc m.support.card ≤ (Finset.univ : Finset Unit).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 1 := by simp

end

end GaloisForLFunctions.BohrGeneratorAxis

namespace GaloisForLFunctions.BohrGeneratorAxis

open Finsupp AddMonoidAlgebra GaloisForLFunctions

noncomputable section

theorem primeLogFrequencyComplex_single (p : Nat.Primes) (k : ℤ) :
    primeLogFrequencyComplex (Finsupp.single p k) = (k : ℂ) * (Real.log (p : ℕ) : ℂ) := by
  rw [primeLogFrequencyComplex, Finsupp.sum_single_index]
  simp

/-- **Every Euler-side term is an axis mode.**  The `p`-lane term `p^{-ks}` of the additive
prime expansion of `∂_s log ζ` is realized by the single-lane mode `k·δ_p`. -/
theorem eulerTerm_axisMode (p : Nat.Primes) (k : ℤ) :
    (Finsupp.single p k : PrimeMode) ∈ axisSet ∧
      ∀ s : ℂ, archimedeanPrimeMode (Finsupp.single p k) s
        = Complex.exp (-(s * ((k : ℂ) * (Real.log (p : ℕ) : ℂ)))) := by
  refine ⟨axisSet_single p k, fun s => ?_⟩
  rw [archimedeanPrimeMode, primeLogFrequencyComplex_single]

/-- **The generator-level axis-mode law.**

Both generators of the completed `(σ_p, ∂_s)`-connection are Fourier-diagonal; the archimedean
generator is the finite prime sum `-Σ_p (log p) θ_p` on every mode; the whole algebra they generate
preserves the axis-mode submodule; and combination modes are produced by the ring product alone. -/
theorem generatorLevel_axisMode_law :
    (∀ (p : Nat.Primes) (m : PrimeMode),
        sigmaOp p (mode m) = (((p : ℕ) : ℂ) ^ (-(m p))) • mode m) ∧
      (∀ (p : Nat.Primes) (m : PrimeMode), thetaOp p (mode m) = ((m p : ℤ) : ℂ) • mode m) ∧
      (∀ m : PrimeMode, dsOp (mode m) = (-primeLogFrequencyComplex m) • mode m) ∧
      (∀ m : PrimeMode,
        dsOp (mode m) = -∑ p ∈ m.support, (Real.log (p : ℕ) : ℂ) • thetaOp p (mode m)) ∧
      (∀ p : Nat.Primes, sigmaOp p * dsOp = dsOp * sigmaOp p) ∧
      (∀ T ∈ generatorAlgebra, ∀ a ∈ axisSupported, T a ∈ axisSupported) ∧
      (∀ p q : Nat.Primes, p ≠ q → ∀ k l : ℤ, k ≠ 0 → l ≠ 0 →
        mode (Finsupp.single p k) ∈ axisSupported ∧
          mode (Finsupp.single q l) ∈ axisSupported ∧
          mode (Finsupp.single p k) * mode (Finsupp.single q l) ∉ axisSupported) :=
  ⟨sigmaOp_mode, thetaOp_mode, dsOp_mode, dsOp_mode_eq_neg_sum, sigmaOp_dsOp_commute,
    fun _ hT _ ha => generatorAlgebra_preserves_axisSupported hT ha,
    fun p q hpq k l hk hl =>
      let h := twoAxis_product_not_mem_axisSupported hpq hk hl
      ⟨h.1, h.2.1, h.2.2.2⟩⟩

end

end GaloisForLFunctions.BohrGeneratorAxis
