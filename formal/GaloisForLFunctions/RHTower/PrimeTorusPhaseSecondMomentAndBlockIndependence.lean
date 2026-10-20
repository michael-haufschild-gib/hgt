import GaloisForLFunctions.HTGeometry.TorusConditionalProductL2
import GaloisForLFunctions.HTGeometry.BohrOrbitClosure
import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import Mathlib.Probability.Independence.Basic

/-!
# Prime phases on the torus: orthogonality, second moments, and block independence

On the prime torus `UnitAddTorus Nat.Primes` with its Haar probability measure, the phase of a
point at a prime `p` is `torusPrimePhase p x = e^{2πi x_p}`, the `p`-th circle coordinate.  Three facts about these phases drive the
uniform lower bound for Euler-product return densities.

* **Orthogonality**: `∫ conj(X_p) X_q dHaar = δ_{pq}` (`integral_conj_torusPrimePhase_mul`), a
  character integral.
* **Second moment**: for vectors `u p` of a Hilbert space,
  `∫ ‖Σ_{p∈S} X_p • u p‖² dHaar = Σ_{p∈S} ‖u p‖²` (`integral_normSq_torusPrimePhase_sum`), hence the
  Chebyshev bound `Haar{‖Σ X_p • u p‖ ≥ δ} ≤ Σ‖u p‖²/δ²` (`measure_torusPrimePhase_sum_ge_le`).
* **Block independence**: events depending on disjoint finite sets of coordinates are independent
  (`torusHaar_inter_eq_mul_of_disjoint_blocks`), since Haar measure is the infinite product of the
  circle Haar measures; an event that depends only on the coordinates in `S` is a cylinder over
  `S` (`setOf_mem_eq_restrict_preimage`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace RHTower

/-! ## Prime phases -/

/-- The phase of a torus point at the prime `p`, as a complex number of modulus one. -/
def torusPrimePhase (p : Nat.Primes) (x : UnitAddTorus Nat.Primes) : ℂ :=
  ((unitTorusHomeomorphCircles Nat.Primes x p : Circle) : ℂ)

theorem unitTorusHomeomorphCircles_apply_toCircle (x : UnitAddTorus Nat.Primes) (p : Nat.Primes) :
    unitTorusHomeomorphCircles Nat.Primes x p = (x p).toCircle := by
  unfold unitTorusHomeomorphCircles
  rw [Homeomorph.piCongrRight_apply, AddCircle.homeomorphCircle_apply]

/-- The circle coordinates only read their own torus coordinate. -/
theorem unitTorusHomeomorphCircles_apply_congr {p : Nat.Primes} {x x' : UnitAddTorus Nat.Primes}
    (h : x p = x' p) :
    unitTorusHomeomorphCircles Nat.Primes x p = unitTorusHomeomorphCircles Nat.Primes x' p := by
  rw [unitTorusHomeomorphCircles_apply_toCircle, unitTorusHomeomorphCircles_apply_toCircle, h]

theorem torusPrimePhase_eq_fourier (p : Nat.Primes) (x : UnitAddTorus Nat.Primes) :
    torusPrimePhase p x = fourier 1 (x p) := by
  unfold torusPrimePhase unitTorusHomeomorphCircles
  rw [Homeomorph.piCongrRight_apply, AddCircle.homeomorphCircle_apply, fourier_apply, one_zsmul]

theorem norm_torusPrimePhase (p : Nat.Primes) (x : UnitAddTorus Nat.Primes) : ‖torusPrimePhase p x‖ = 1 :=
  Circle.norm_coe _

theorem continuous_torusPrimePhase (p : Nat.Primes) : Continuous (torusPrimePhase p) := by
  unfold torusPrimePhase
  exact continuous_subtype_val.comp
    ((continuous_apply p).comp (unitTorusHomeomorphCircles Nat.Primes).continuous)

/-- The phases only read their own coordinate. -/
theorem torusPrimePhase_congr {p : Nat.Primes} {x x' : UnitAddTorus Nat.Primes} (h : x p = x' p) :
    torusPrimePhase p x = torusPrimePhase p x' := by
  rw [torusPrimePhase_eq_fourier, torusPrimePhase_eq_fourier, h]

/-- **Orthogonality of the prime phases.** -/
theorem integral_conj_torusPrimePhase_mul (p q : Nat.Primes) :
    ∫ x, conj (torusPrimePhase p x) * torusPrimePhase q x ∂(torusHaar Nat.Primes)
      = if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true]
    have hone : ∀ x : UnitAddTorus Nat.Primes, conj (torusPrimePhase p x) * torusPrimePhase p x = 1 := by
      intro x
      rw [torusPrimePhase_eq_fourier, ← fourier_neg, ← fourier_add]
      simp
    simp only [hone, integral_const, probReal_univ, one_smul]
  · rw [if_neg hpq]
    set n : Nat.Primes →₀ ℤ := Finsupp.single q 1 - Finsupp.single p 1 with hn
    have hnp : n p = -1 := by
      rw [hn, Finsupp.sub_apply, Finsupp.single_eq_of_ne hpq, Finsupp.single_eq_same]
      ring
    have hnq : n q = 1 := by
      rw [hn, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hpq)]
      ring
    have hsupp : n.support ⊆ {p, q} := by
      refine Finsupp.support_sub.trans ?_
      rw [Finsupp.support_single _ one_ne_zero, Finsupp.support_single _ one_ne_zero]
      intro i hi
      simp only [mem_union, mem_singleton] at hi
      simp only [mem_insert, mem_singleton]
      tauto
    have hchar : ∀ x : UnitAddTorus Nat.Primes,
        conj (torusPrimePhase p x) * torusPrimePhase q x = torusCharacter n x := by
      intro x
      rw [torusCharacter_apply_of_subset hsupp, Finset.prod_pair hpq, hnp, hnq,
        torusPrimePhase_eq_fourier, torusPrimePhase_eq_fourier, ← fourier_neg]
    simp only [hchar]
    rw [integral_torusCharacter, if_neg]
    intro h0
    have := congrArg (fun f : Nat.Primes →₀ ℤ => f q) h0
    rw [hnq] at this
    simp at this

/-! ## Second moments of random finite sums -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The random finite sum `Σ_{p∈S} X_p(x) • u p`. -/
def torusPrimePhaseSum (S : Finset Nat.Primes) (u : Nat.Primes → H) (x : UnitAddTorus Nat.Primes) : H :=
  ∑ p ∈ S, torusPrimePhase p x • u p

theorem continuous_torusPrimePhaseSum (S : Finset Nat.Primes) (u : Nat.Primes → H) :
    Continuous (torusPrimePhaseSum S u) :=
  continuous_finsetSum _ fun p _ => (continuous_torusPrimePhase p).smul continuous_const

theorem torusPrimePhaseSum_congr {S : Finset Nat.Primes} (u : Nat.Primes → H)
    {x x' : UnitAddTorus Nat.Primes} (h : ∀ p ∈ S, x p = x' p) :
    torusPrimePhaseSum S u x = torusPrimePhaseSum S u x' :=
  sum_congr rfl fun p hp => by rw [torusPrimePhase_congr (h p hp)]

/-- The inner product of two random sums expands into phase products. -/
theorem inner_torusPrimePhaseSum (S : Finset Nat.Primes) (u : Nat.Primes → H)
    (x : UnitAddTorus Nat.Primes) :
    ⟪torusPrimePhaseSum S u x, torusPrimePhaseSum S u x⟫_ℂ
      = ∑ p ∈ S, ∑ q ∈ S, conj (torusPrimePhase p x) * torusPrimePhase q x * ⟪u p, u q⟫_ℂ := by
  unfold torusPrimePhaseSum
  rw [sum_inner]
  refine sum_congr rfl fun p _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem integrable_continuous_torus {E : Type*} [NormedAddCommGroup E] {f : UnitAddTorus Nat.Primes → E}
    (hf : Continuous f) : Integrable f (torusHaar Nat.Primes) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Second moment**: `∫ ‖Σ_{p∈S} X_p • u p‖² = Σ_{p∈S} ‖u p‖²`. -/
theorem integral_normSq_torusPrimePhaseSum (S : Finset Nat.Primes) (u : Nat.Primes → H) :
    ∫ x, ‖torusPrimePhaseSum S u x‖ ^ 2 ∂(torusHaar Nat.Primes) = ∑ p ∈ S, ‖u p‖ ^ 2 := by
  classical
  -- the squared norm is the real part of the expanded inner product
  have hre : ∀ x : UnitAddTorus Nat.Primes, ‖torusPrimePhaseSum S u x‖ ^ 2
      = RCLike.re (∑ p ∈ S, ∑ q ∈ S, conj (torusPrimePhase p x) * torusPrimePhase q x * ⟪u p, u q⟫_ℂ) := by
    intro x
    rw [← inner_torusPrimePhaseSum, inner_self_eq_norm_sq]
  have hint : ∀ p q : Nat.Primes, Integrable
      (fun x : UnitAddTorus Nat.Primes => conj (torusPrimePhase p x) * torusPrimePhase q x * ⟪u p, u q⟫_ℂ)
      (torusHaar Nat.Primes) :=
    fun p q => integrable_continuous_torus
      ((Complex.continuous_conj.comp (continuous_torusPrimePhase p)).mul (continuous_torusPrimePhase q)
        |>.mul continuous_const)
  have hintsum : Integrable (fun x : UnitAddTorus Nat.Primes =>
      ∑ p ∈ S, ∑ q ∈ S, conj (torusPrimePhase p x) * torusPrimePhase q x * ⟪u p, u q⟫_ℂ)
      (torusHaar Nat.Primes) :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q
  simp_rw [hre]
  rw [integral_re hintsum, integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  have hinner : ∀ p ∈ S, (∫ x, ∑ q ∈ S, conj (torusPrimePhase p x) * torusPrimePhase q x * ⟪u p, u q⟫_ℂ
      ∂(torusHaar Nat.Primes)) = ⟪u p, u p⟫_ℂ := by
    intro p hp
    rw [integral_finsetSum _ fun q _ => hint p q]
    have hterm : ∀ q ∈ S, (∫ x, conj (torusPrimePhase p x) * torusPrimePhase q x * ⟪u p, u q⟫_ℂ
        ∂(torusHaar Nat.Primes)) = if p = q then ⟪u p, u q⟫_ℂ else 0 := by
      intro q _
      rw [integral_mul_const, integral_conj_torusPrimePhase_mul]
      split_ifs <;> simp
    rw [sum_congr rfl hterm, Finset.sum_ite_eq, if_pos hp]
  rw [sum_congr rfl hinner, map_sum]
  exact sum_congr rfl fun p _ => inner_self_eq_norm_sq (u p)

/-- **Chebyshev for the random sum.** -/
theorem measure_torusPrimePhaseSum_ge_le (S : Finset Nat.Primes) (u : Nat.Primes → H) {δ : ℝ}
    (hδ : 0 < δ) :
    torusHaar Nat.Primes {x | δ ≤ ‖torusPrimePhaseSum S u x‖}
      ≤ ENNReal.ofReal ((∑ p ∈ S, ‖u p‖ ^ 2) / δ ^ 2) := by
  have hf : Integrable (fun x : UnitAddTorus Nat.Primes => ‖torusPrimePhaseSum S u x‖ ^ 2)
      (torusHaar Nat.Primes) :=
    integrable_continuous_torus ((continuous_torusPrimePhaseSum S u).norm.pow 2)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := torusHaar Nat.Primes)
    (f := fun x => ‖torusPrimePhaseSum S u x‖ ^ 2) (Eventually.of_forall fun x => by positivity) hf
    (δ ^ 2)
  rw [integral_normSq_torusPrimePhaseSum] at hmarkov
  have hsub : {x : UnitAddTorus Nat.Primes | δ ≤ ‖torusPrimePhaseSum S u x‖}
      ⊆ {x | δ ^ 2 ≤ ‖torusPrimePhaseSum S u x‖ ^ 2} :=
    fun x hx => pow_le_pow_left₀ hδ.le hx 2
  have hmono : (torusHaar Nat.Primes).real {x | δ ≤ ‖torusPrimePhaseSum S u x‖}
      ≤ (torusHaar Nat.Primes).real {x | δ ^ 2 ≤ ‖torusPrimePhaseSum S u x‖ ^ 2} :=
    measureReal_mono hsub (measure_ne_top (torusHaar Nat.Primes) _)
  have hreal : (torusHaar Nat.Primes).real {x | δ ≤ ‖torusPrimePhaseSum S u x‖}
      ≤ (∑ p ∈ S, ‖u p‖ ^ 2) / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (torusHaar Nat.Primes).real {x | δ ≤ ‖torusPrimePhaseSum S u x‖} * δ ^ 2
        ≤ (torusHaar Nat.Primes).real {x | δ ^ 2 ≤ ‖torusPrimePhaseSum S u x‖ ^ 2} * δ ^ 2 :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
      _ ≤ ∑ p ∈ S, ‖u p‖ ^ 2 := by linarith
  calc torusHaar Nat.Primes {x | δ ≤ ‖torusPrimePhaseSum S u x‖}
      = ENNReal.ofReal ((torusHaar Nat.Primes).real {x | δ ≤ ‖torusPrimePhaseSum S u x‖}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((∑ p ∈ S, ‖u p‖ ^ 2) / δ ^ 2) := ENNReal.ofReal_le_ofReal hreal

/-! ## Block independence -/

/-- The coordinates of a torus point in the block `S`. -/
def torusBlockRestrict (S : Finset Nat.Primes) (x : UnitAddTorus Nat.Primes) : S → UnitAddCircle :=
  fun p => x p

/-- Extension of a block of coordinates by zero. -/
def blockExtendTorus (S : Finset Nat.Primes) (v : S → UnitAddCircle) : UnitAddTorus Nat.Primes :=
  fun p => if h : p ∈ S then v ⟨p, h⟩ else 0

theorem blockExtendTorus_apply_of_mem (S : Finset Nat.Primes) (v : S → UnitAddCircle) {p : Nat.Primes}
    (hp : p ∈ S) : blockExtendTorus S v p = v ⟨p, hp⟩ := dif_pos hp

theorem blockExtendTorus_torusBlockRestrict_apply (S : Finset Nat.Primes) (x : UnitAddTorus Nat.Primes)
    {p : Nat.Primes} (hp : p ∈ S) : blockExtendTorus S (torusBlockRestrict S x) p = x p :=
  dif_pos hp

theorem continuous_blockExtendTorus (S : Finset Nat.Primes) : Continuous (blockExtendTorus S) := by
  refine continuous_pi fun p => ?_
  unfold blockExtendTorus
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem measurable_torusBlockRestrict (S : Finset Nat.Primes) : Measurable (torusBlockRestrict S) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : Nat.Primes)

theorem continuous_torusBlockRestrict (S : Finset Nat.Primes) : Continuous (torusBlockRestrict S) :=
  continuous_pi fun i => continuous_apply (i : Nat.Primes)

/-- **An event depending only on the coordinates in `S` is a cylinder over `S`.** -/
theorem setOf_mem_eq_torusBlockRestrict_preimage {S : Finset Nat.Primes} {α : Type*}
    {Φ : UnitAddTorus Nat.Primes → α}
    (hΦ : ∀ x, Φ (blockExtendTorus S (torusBlockRestrict S x)) = Φ x) (W : Set α) :
    {x | Φ x ∈ W} = {x | torusBlockRestrict S x ∈ blockExtendTorus S ⁻¹' (Φ ⁻¹' W)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hΦ x]

/-- **An open set determined by the coordinates in `S` is a cylinder over `S` with open base.** -/
theorem eq_setOf_torusBlockRestrict_mem_of_determined {S : Finset Nat.Primes}
    {V : Set (UnitAddTorus Nat.Primes)}
    (hV : ∀ x, blockExtendTorus S (torusBlockRestrict S x) ∈ V ↔ x ∈ V) :
    V = {x | torusBlockRestrict S x ∈ blockExtendTorus S ⁻¹' V} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hV x]

theorem isOpen_blockExtendTorus_preimage (S : Finset Nat.Primes)
    {V : Set (UnitAddTorus Nat.Primes)} (hV : IsOpen V) : IsOpen (blockExtendTorus S ⁻¹' V) :=
  hV.preimage (continuous_blockExtendTorus S)

/-- A continuous observable that depends only on the coordinates in `S` gives measurable cylinder
data for every open target set. -/
theorem measurableSet_cylinder_of_continuous {S : Finset Nat.Primes} {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {Φ : UnitAddTorus Nat.Primes → α} (hΦc : Continuous Φ) {W : Set α} (hW : IsOpen W) :
    MeasurableSet (blockExtendTorus S ⁻¹' (Φ ⁻¹' W)) :=
  (hW.preimage (hΦc.comp (continuous_blockExtendTorus S))).measurableSet

/-- **Disjoint coordinate blocks are independent under Haar measure.** -/
theorem torusHaar_inter_eq_mul_of_disjoint_blocks {S T : Finset Nat.Primes} (hST : Disjoint S T)
    {E : Set (S → UnitAddCircle)} {F : Set (T → UnitAddCircle)} (hE : MeasurableSet E)
    (hF : MeasurableSet F) :
    torusHaar Nat.Primes ({x | torusBlockRestrict S x ∈ E} ∩ {x | torusBlockRestrict T x ∈ F})
      = torusHaar Nat.Primes {x | torusBlockRestrict S x ∈ E}
        * torusHaar Nat.Primes {x | torusBlockRestrict T x ∈ F} := by
  rw [torusHaar_eq_infinitePi]
  have hind := ProbabilityTheory.iIndepFun.indepFun_finset S T hST
    (ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : Nat.Primes => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (X := fun (_ : Nat.Primes) (ω : UnitAddCircle) => ω) fun _ => measurable_id)
    (fun i => measurable_pi_apply i)
  exact hind.measure_inter_preimage_eq_mul E F hE hF

end RHTower
