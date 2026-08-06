import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The frequency rank of a set of integer characters

A finite family of rationally independent real frequencies turns integer
characters into real frequencies injectively.  This file proves that the
resulting map does not lose rank: the rational rank of the frequency set is
exactly the integer rank of the character lattice it comes from.

Two ingredients:

* the integer rank of a set inside a rational vector space is its rational
  rank, because a maximal rationally independent subset is integrally
  independent and conversely;
* rational independence of the frequency family says exactly that the rational
  character-detuning functional is injective, which is obtained by clearing
  denominators.

For a quasiperiodic function built from a Laurent expansion, this identifies
the rational rank of its Bohr frequency module with the integer rank of its
active exponent lattice.
-/

open scoped BigOperators
open Cardinal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Integer rank inside a rational vector space -/

/-- **Integer rank is rational rank.**  Inside a rational vector space, the
integer span of a set has the same rank as its rational span. -/
theorem rank_span_int_eq_rank_span_rat {M : Type*} [AddCommGroup M] [Module ℚ M]
    (T : Set M) :
    Module.rank ℤ (Submodule.span ℤ T) = Module.rank ℚ (Submodule.span ℚ T) := by
  refine le_antisymm ?_ ?_
  · have hsub : ∀ x : Submodule.span ℤ T, (x : M) ∈ Submodule.span ℚ T := by
      intro x
      have hle : Submodule.span ℤ T ≤ (Submodule.span ℚ T).restrictScalars ℤ := by
        rw [Submodule.span_le]
        exact fun y hy => Submodule.subset_span hy
      exact hle x.2
    let g : (Submodule.span ℤ T) →ₗ[ℤ] (Submodule.span ℚ T) :=
      { toFun := fun x => ⟨(x : M), hsub x⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hginj : Function.Injective g := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : Submodule.span ℚ T => (z : M)) hxy)
    calc Module.rank ℤ (Submodule.span ℤ T)
        ≤ Module.rank ℤ (Submodule.span ℚ T) := LinearMap.rank_le_of_injective g hginj
      _ = Module.rank ℚ (Submodule.span ℚ T) :=
          (IsLocalization.rank_eq ℚ (nonZeroDivisors ℤ) le_rfl).symm
  · obtain ⟨b, hbT, hspan, hind⟩ := exists_linearIndependent ℚ T
    have hZ : LinearIndependent ℤ (Subtype.val : b → M) :=
      (LinearIndependent.iff_fractionRing ℤ ℚ).2 hind
    have hQ : Module.rank ℚ (Submodule.span ℚ T) = #b := by
      rw [← hspan]
      exact rank_span_set hind
    have hI : Module.rank ℤ (Submodule.span ℤ b) = #b := rank_span_set hZ
    rw [hQ, ← hI]
    exact Submodule.rank_mono (Submodule.span_mono hbT)

/-! ### Rational characters of a finite frequency family -/

variable {d : Type} [Fintype d]

/-- Integer characters read as rational characters. -/
def intCharacterToRat : (d → ℤ) →ₗ[ℤ] (d → ℚ) where
  toFun m := fun i => (m i : ℚ)
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp

omit [Fintype d] in
@[simp] theorem intCharacterToRat_apply (m : d → ℤ) (i : d) :
    intCharacterToRat m i = (m i : ℚ) := rfl

omit [Fintype d] in
theorem injective_intCharacterToRat :
    Function.Injective (intCharacterToRat (d := d)) := by
  intro a b hab
  funext i
  have := congrFun hab i
  simp only [intCharacterToRat_apply] at this
  exact_mod_cast this

/-- The detuning of a rational character against a frequency family. -/
def ratCharacterDetuning (omega : d → ℝ) : (d → ℚ) →ₗ[ℚ] ℝ :=
  ∑ i, omega i • ((Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))

theorem ratCharacterDetuning_apply (omega : d → ℝ) (q : d → ℚ) :
    ratCharacterDetuning omega q = ∑ i, (q i : ℝ) * omega i := by
  simp only [ratCharacterDetuning, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.proj_apply, Algebra.linearMap_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_ratCast (algebraMap ℚ ℝ) (q i)]
  ring

theorem ratCharacterDetuning_intCharacterToRat (omega : d → ℝ) (m : d → ℤ) :
    ratCharacterDetuning omega (intCharacterToRat m) =
      finiteTorusCharacterDetuning m omega := by
  rw [ratCharacterDetuning_apply, finiteTorusCharacterDetuning]
  exact Finset.sum_congr rfl fun i _ => by norm_num

/-- A common denominator turns a rational character into an integer one. -/
theorem exists_intCharacter_of_ratCharacter [DecidableEq d] (q : d → ℚ) :
    ∃ (N : ℕ) (n : d → ℤ), N ≠ 0 ∧ ∀ i, ((n i : ℤ) : ℚ) = (N : ℚ) * q i := by
  classical
  refine ⟨∏ j, (q j).den,
    fun i => (∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)) * (q i).num,
    ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Rat.den_ne_zero (q j)
  · intro i
    have hden : ((q i).den : ℚ) * q i = ((q i).num : ℚ) := by
      rw [mul_comm]; exact Rat.mul_den_eq_num (q i)
    have hsplit : (∏ j, (q j).den) =
        (∏ j ∈ Finset.univ.erase i, (q j).den) * (q i).den :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [hsplit]
    push_cast
    rw [mul_assoc, hden]

/-- **Rational independence is injectivity of the rational detuning.** -/
theorem injective_ratCharacterDetuning [DecidableEq d] {omega : d → ℝ}
    (h : RationallyIndependentFrequency omega) :
    Function.Injective (ratCharacterDetuning omega) := by
  classical
  have hzero : ∀ q : d → ℚ, ratCharacterDetuning omega q = 0 → q = 0 := by
    intro q hq
    obtain ⟨N, n, hN, hn⟩ := exists_intCharacter_of_ratCharacter q
    rw [ratCharacterDetuning_apply] at hq
    have hcast : ∀ i, ((n i : ℤ) : ℝ) = (N : ℝ) * (q i : ℝ) := by
      intro i
      have := congrArg (fun x : ℚ => (x : ℝ)) (hn i)
      push_cast at this
      exact this
    have hdet : finiteTorusCharacterDetuning n omega = 0 := by
      have hsum : finiteTorusCharacterDetuning n omega =
          (N : ℝ) * ∑ i, (q i : ℝ) * omega i := by
        rw [finiteTorusCharacterDetuning, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hcast i]; ring
      rw [hsum, hq, mul_zero]
    have hn0 : n = 0 := h n hdet
    funext i
    have hi := hn i
    rw [hn0] at hi
    simp only [Pi.zero_apply, Int.cast_zero] at hi
    have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN
    have := (mul_eq_zero.1 hi.symm).resolve_left hNQ
    simpa using this
  intro a b hab
  have h0 : ratCharacterDetuning omega (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.1 (hzero _ h0)

/-! ### The frequency rank of a character set -/

/-- The real frequencies produced by a set of integer characters. -/
def characterFrequencySet (omega : d → ℝ) (S : Set (d → ℤ)) : Set ℝ :=
  (fun m => finiteTorusCharacterDetuning m omega) '' S

/-- **The frequency rank is the character rank.**  For a rationally
independent frequency family, the rational rank of the frequencies produced by
a set of integer characters equals the integer rank of the lattice that set
generates. -/
theorem rank_span_characterFrequencySet [DecidableEq d] {omega : d → ℝ}
    (h : RationallyIndependentFrequency omega) (S : Set (d → ℤ)) :
    Module.rank ℚ (Submodule.span ℚ (characterFrequencySet omega S)) =
      Module.rank ℤ (Submodule.span ℤ S) := by
  classical
  have hmapInt :
      Module.rank ℤ (Submodule.span ℤ S) =
        Module.rank ℤ (Submodule.span ℤ (intCharacterToRat (d := d) '' S)) := by
    rw [← Submodule.map_span]
    exact (Submodule.equivMapOfInjective _ injective_intCharacterToRat
      (Submodule.span ℤ S)).rank_eq
  have hbridge :
      Module.rank ℤ (Submodule.span ℤ (intCharacterToRat (d := d) '' S)) =
        Module.rank ℚ (Submodule.span ℚ (intCharacterToRat (d := d) '' S)) :=
    rank_span_int_eq_rank_span_rat _
  have himage :
      (ratCharacterDetuning omega) '' (intCharacterToRat (d := d) '' S) =
        characterFrequencySet omega S := by
    rw [← Set.image_comp]
    exact Set.image_congr fun m _ => ratCharacterDetuning_intCharacterToRat omega m
  have hmapRat :
      Module.rank ℚ (Submodule.span ℚ (intCharacterToRat (d := d) '' S)) =
        Module.rank ℚ (Submodule.span ℚ (characterFrequencySet omega S)) := by
    rw [← himage, ← Submodule.map_span]
    exact (Submodule.equivMapOfInjective _ (injective_ratCharacterDetuning h)
      (Submodule.span ℚ (intCharacterToRat (d := d) '' S))).rank_eq
  rw [hmapInt, hbridge, hmapRat]

end

end GaloisForLFunctions.HTGeometry
