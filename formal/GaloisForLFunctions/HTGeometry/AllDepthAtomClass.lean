import GaloisForLFunctions.HTGeometry.AllDepthBottomRealization
import GaloisForLFunctions.HTGeometry.TripticJetAtomShift
import GaloisForLFunctions.HTGeometry.TripticNormalForm

/-!
# The atom realization lies in the all-depth class

The atom sum built to realize a prescribed bottom charge must itself be a member of the
mixed-constraint class, so that the difference of a source and its realization stays in the class.
A jet atom drops by a constant under a step in its own lattice direction and is unchanged under a
step in any other, so the full difference cube of an atom sum vanishes as soon as at least two
directions remain.

* `shiftConstGerm_jetAtom`, `shiftConstGerm_multiAtomRealization`;
* `eventually_zero_diffCube`, `mixedConstGermSet_zero_of_shiftConstGerm`;
* **`mixedConstGermSet_multiAtomRealization`**.
-/

open Filter Set Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Germ calculus for the difference cube -/

variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
theorem eventually_zero_diffCube (τ : ι → ℂ) (u : Finset ι) {G : ℂ → ℂ}
    (hG : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, G w = 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, diffCube τ u G w = 0 := by
  classical
  have hall : ∀ E ∈ u.powerset, ∀ᶠ w in 𝓝[≠] z, G (w + ∑ i ∈ E, τ i) = 0 := by
    intro E _
    exact (tendsto_nhdsNE_add_const z (∑ i ∈ E, τ i)).eventually (hG (z + ∑ i ∈ E, τ i))
  rw [← Filter.eventually_all_finset] at hall
  filter_upwards [hall] with w hw
  rw [diffCube]
  exact Finset.sum_eq_zero fun E hE => by rw [hw E hE, mul_zero]

theorem eventually_zero_shiftDiffFun_of_const {G : ℂ → ℂ} {C h : ℂ}
    (hG : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, G w = C) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, shiftDiffFun h G w = 0 := by
  have hpull := (tendsto_nhdsNE_add_const z h).eventually (hG (z + h))
  filter_upwards [hpull, hG z] with w h1 h2
  show G (w + h) - G w = 0
  rw [h1, h2, sub_self]

/-- **A germ-constant step in one direction kills the full cube**, as soon as two further
directions remain. -/
theorem mixedConstGermSet_zero_of_shiftConstGerm {τ : ι → ℂ} {s : Finset ι} {k : ι} (hk : k ∈ s)
    {i : ι} (hi : i ∈ s) (hik : i ≠ k) {G : ℂ → ℂ} {C : ℂ}
    (hG : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, G (w + τ k) - G w = C) :
    MixedConstGermSet τ s G 0 := by
  classical
  have hkunion : (s \ {k}) ∪ ({k} : Finset ι) = s := by
    ext m
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (hm | rfl)
      · exact hm.1
      · exact hk
    · intro hm
      by_cases hmk : m = k
      · exact Or.inr hmk
      · exact Or.inl ⟨hm, hmk⟩
  have hkdisj : Disjoint (s \ {k}) ({k} : Finset ι) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    exact (Finset.mem_sdiff.mp hm).2 hm'
  have hiu : i ∈ s \ {k} := Finset.mem_sdiff.mpr ⟨hi, by simpa using hik⟩
  have hiunion : ((s \ {k}) \ {i}) ∪ ({i} : Finset ι) = s \ {k} := by
    ext m
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (hm | rfl)
      · exact hm.1
      · exact ⟨hi, by simpa using hik⟩
    · intro hm
      by_cases hmi : m = i
      · exact Or.inr hmi
      · exact Or.inl ⟨hm, hmi⟩
  have hidisj : Disjoint ((s \ {k}) \ {i}) ({i} : Finset ι) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    exact (Finset.mem_sdiff.mp hm).2 hm'
  intro z
  have hstep : diffCube τ s G
      = diffCube τ ((s \ {k}) \ {i}) (shiftDiffFun (τ i) (shiftDiffFun (τ k) G)) := by
    have h1 : diffCube τ ((s \ {k}) ∪ ({k} : Finset ι)) G
        = diffCube τ (s \ {k}) (shiftDiffFun (τ k) G) := by
      rw [diffCube_union τ hkdisj, diffCube_singleton]
    have h2 : diffCube τ (((s \ {k}) \ {i}) ∪ ({i} : Finset ι)) (shiftDiffFun (τ k) G)
        = diffCube τ ((s \ {k}) \ {i}) (shiftDiffFun (τ i) (shiftDiffFun (τ k) G)) := by
      rw [diffCube_union τ hidisj, diffCube_singleton]
    rw [hkunion] at h1
    rw [hiunion] at h2
    rw [h1, h2]
  rw [hstep]
  exact eventually_zero_diffCube τ _
    (fun y => eventually_zero_shiftDiffFun_of_const (C := C) hG y) z

/-! ## The step law of a jet atom -/

variable {σ : ℂ}

/-- **A jet atom drops by a constant under a step in its own direction.** -/
theorem shiftConstGerm_jetAtom (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, jetAtom σ q j (w + σ) - jetAtom σ q j w
      = (if j = 0 then -(2 * (Real.pi : ℂ) * Complex.I) else 0) := by
  filter_upwards [eventually_nhdsNE_notMem_atomPoleSet hσ q z] with w hw
  cases j with
  | zero =>
      rw [if_pos rfl]
      show iteratedDeriv 0 (lineAtom σ q) (w + σ) - iteratedDeriv 0 (lineAtom σ q) w = _
      rw [iteratedDeriv_zero]
      have hne : jacobiTheta₂ (w - q) σ ≠ 0 := fun hcon =>
        hw ((mem_atomPoleSet_iff hσ q w).mpr hcon)
      rw [lineAtom_shift hσ q hne]
      ring
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n), jetAtom_shift_succ hσ q n hw, sub_self]

/-- The constant by which a multi-order atom sum steps. -/
def multiAtomConst (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, ∑ q ∈ R, (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
    (if j = 0 then -(2 * (Real.pi : ℂ) * Complex.I) else 0)

/-- **The multi-order atom sum steps by a constant in its own direction.** -/
theorem shiftConstGerm_multiAtomRealization (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, multiAtomRealization σ N R c (w + σ) - multiAtomRealization σ N R c w
      = multiAtomConst N R c := by
  classical
  have hall : ∀ j ∈ Finset.range N, ∀ᶠ w in 𝓝[≠] z, ∀ q ∈ R,
      jetAtom σ (q - thetaHalfPeriod σ) j (w + σ) - jetAtom σ (q - thetaHalfPeriod σ) j w
        = (if j = 0 then -(2 * (Real.pi : ℂ) * Complex.I) else 0) := by
    intro j _
    rw [Filter.eventually_all_finset]
    exact fun q _ => shiftConstGerm_jetAtom hσ _ j z
  rw [← Filter.eventually_all_finset] at hall
  filter_upwards [hall] with w hw
  show (∑ j ∈ Finset.range N, atomRealization σ j R (c j) (w + σ))
      - ∑ j ∈ Finset.range N, atomRealization σ j R (c j) w = multiAtomConst N R c
  rw [← Finset.sum_sub_distrib, multiAtomConst]
  refine Finset.sum_congr rfl fun j hj => ?_
  show (∑ q ∈ R, (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
        jetAtom σ (q - thetaHalfPeriod σ) j (w + σ))
      - ∑ q ∈ R, (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
        jetAtom σ (q - thetaHalfPeriod σ) j w = _
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← mul_sub, hw j hj q hq]

/-- **The atom realization is a member of the all-depth class with constant zero.** -/
theorem mixedConstGermSet_multiAtomRealization {τ : ι → ℂ} {s : Finset ι} {k : ι} (hk : k ∈ s)
    {i : ι} (hi : i ∈ s) (hik : i ≠ k) (hσ : 0 < (τ k).im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) :
    MixedConstGermSet τ s (multiAtomRealization (τ k) N R c) 0 :=
  mixedConstGermSet_zero_of_shiftConstGerm hk hi hik
    (C := multiAtomConst N R c) (shiftConstGerm_multiAtomRealization hσ N R c)

theorem periodicOneGerm_multiAtomRealization (σ : ℂ) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    PeriodicOneGerm (multiAtomRealization σ N R c) := by
  intro z
  filter_upwards with w
  exact multiAtomRealization_periodic σ N R c w

end

end GaloisForLFunctions.HTGeometry
