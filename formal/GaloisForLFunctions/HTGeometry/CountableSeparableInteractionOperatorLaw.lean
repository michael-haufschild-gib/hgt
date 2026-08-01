import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionSaturationLaw
import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality
import GaloisForLFunctions.RHTower.MaximalRealDiagonalSelfAdjoint
import GaloisForLFunctions.RHTower.TraceNormBound

/-!
# Countable separable-interaction operator law

The countable saturation theorem constructs an absolutely summable real
diagonal interaction profile.  This file promotes that arithmetic profile
to a genuine bounded quantum perturbation on `ℓ²`: it is self-adjoint,
Schatten-1, and arbitrarily small in operator norm.

The same saturated countable spectrum controls every finite spectral
window.  Consequently every positive-weight finite window reaches the
permutation collision floor at every replica order.  Infinite weak
interaction and finite all-order recurrence extremality are therefore two
consequences of one perturbation, rather than separate genericity claims.
-/

open scoped BigOperators InnerProductSpace LinearPMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Absolute summability of a real diagonal implies square summability of
its complex multiplier. -/
theorem summable_norm_real_cast_sq
    {I : Type*} (w : I → ℝ) (habs : Summable (fun i => |w i|)) :
    Summable (fun i => ‖(w i : ℂ)‖ ^ 2) := by
  let C : ℝ := max 1 (∑' i, |w i|)
  have hC : ∀ i, |w i| ≤ C := by
    intro i
    exact (habs.le_tsum i (fun j _ => abs_nonneg (w j))).trans
      (le_max_right _ _)
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg ‖(w i : ℂ)‖) (fun i => ?_)
    (habs.mul_left C)
  rw [Complex.norm_real, Real.norm_eq_abs]
  nlinarith [abs_nonneg (w i), hC i]

/-- The principal complex square roots of an absolutely summable real
diagonal form a square-summable multiplier. -/
theorem summable_norm_complex_sqrt_real_sq
    {I : Type*} (w : I → ℝ) (habs : Summable (fun i => |w i|)) :
    Summable (fun i => ‖Complex.sqrt (w i : ℂ)‖ ^ 2) := by
  apply habs.congr
  intro i
  rw [← norm_pow, complex_sqrt_sq, Complex.norm_real, Real.norm_eq_abs]

/-- A Hilbert--Schmidt diagonal kernel acts by coordinate multiplication. -/
theorem toOperator_diagMul_apply
    {I : Type*} [DecidableEq I] (g : I → ℂ)
    (hs : Summable (fun i => ‖g i‖ ^ 2))
    (f : lp (fun _ : I => ℂ) 2) (i : I) :
    HilbertSchmidt.toOperator
        (HilbertSchmidt.isHS_diagMul_infinite g hs) f i =
      g i * f i := by
  rw [HilbertSchmidt.toOperator_apply]
  rw [tsum_eq_single i]
  · simp [HilbertSchmidt.diagMul]
  · intro j hji
    simp [HilbertSchmidt.diagMul, Ne.symm hji]

/-- The bounded diagonal operator associated with an absolutely summable
real interaction profile. -/
noncomputable def realSummableDiagonalOperator
    {I : Type*} (w : I → ℝ)
    (habs : Summable (fun i => |w i|)) :
    lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  letI := Classical.decEq I
  HilbertSchmidt.toOperator
    (HilbertSchmidt.isHS_diagMul_infinite (fun i => (w i : ℂ))
      (summable_norm_real_cast_sq w habs))

@[simp] theorem realSummableDiagonalOperator_apply
    {I : Type*} (w : I → ℝ)
    (habs : Summable (fun i => |w i|))
    (f : lp (fun _ : I => ℂ) 2) (i : I) :
    realSummableDiagonalOperator w habs f i =
      (w i : ℂ) * f i := by
  classical
  unfold realSummableDiagonalOperator
  exact toOperator_diagMul_apply (fun i => (w i : ℂ))
    (summable_norm_real_cast_sq w habs) f i

/-- A real diagonal kernel equals its Hilbert--Schmidt adjoint. -/
theorem hsAdjoint_diagMul_real
    {I : Type*} [DecidableEq I] (w : I → ℝ) :
    HilbertSchmidt.hsAdjoint
        (HilbertSchmidt.diagMul (fun i => (w i : ℂ))) =
      HilbertSchmidt.diagMul (fun i => (w i : ℂ)) := by
  funext p
  rcases p with ⟨i, j⟩
  by_cases h : i = j
  · subst j
    simp [HilbertSchmidt.hsAdjoint, HilbertSchmidt.diagMul]
  · simp [HilbertSchmidt.hsAdjoint, HilbertSchmidt.diagMul,
      h, Ne.symm h]

/-- Absolutely summable real diagonals define bounded self-adjoint
operators. -/
theorem realSummableDiagonalOperator_isSelfAdjoint
    {I : Type*} (w : I → ℝ)
    (habs : Summable (fun i => |w i|)) :
    IsSelfAdjoint (realSummableDiagonalOperator w habs) := by
  classical
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  unfold realSummableDiagonalOperator
  rw [HilbertSchmidt.adjoint_toOperator]
  have hk := hsAdjoint_diagMul_real w
  ext f i
  rw [HilbertSchmidt.toOperator_apply,
    HilbertSchmidt.toOperator_apply]
  apply tsum_congr
  intro j
  rw [congrFun hk (i, j)]

/-- Absolutely summable real diagonals are Schatten-1.  Factor the
diagonal through two Hilbert--Schmidt complex square-root diagonals. -/
theorem realSummableDiagonalOperator_memSchattenClass_one
    {I : Type*} (w : I → ℝ)
    (habs : Summable (fun i => |w i|)) :
    RHTower.MemSchattenClass 1
      (realSummableDiagonalOperator w habs) := by
  classical
  let root : I → ℂ := fun i => Complex.sqrt (w i : ℂ)
  have hroot : Summable (fun i => ‖root i‖ ^ 2) :=
    summable_norm_complex_sqrt_real_sq w habs
  let A : lp (fun _ : I => ℂ) 2 →L[ℂ]
      lp (fun _ : I => ℂ) 2 :=
    HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_diagMul_infinite root hroot)
  have hA : A.IsHilbertSchmidt :=
    HilbertSchmidt.isHilbertSchmidt_toOperator
      (HilbertSchmidt.isHS_diagMul_infinite root hroot)
  have hfactor : realSummableDiagonalOperator w habs = A ∘L A := by
    ext f i
    rw [realSummableDiagonalOperator_apply]
    change (w i : ℂ) * f i = A (A f) i
    rw [show A (A f) i = root i * (A f) i by
      exact toOperator_diagMul_apply root hroot (A f) i]
    rw [show A f i = root i * f i by
      exact toOperator_diagMul_apply root hroot f i]
    rw [← mul_assoc, ← pow_two, complex_sqrt_sq]
  rw [hfactor]
  exact RHTower.memSchattenClass_one_comp hA hA

/-- The operator norm of an absolutely summable real diagonal is bounded
by any uniform pointwise bound on its entries. -/
theorem norm_realSummableDiagonalOperator_le
    {I : Type*} (w : I → ℝ)
    (habs : Summable (fun i => |w i|))
    (δ : ℝ) (hδ : 0 ≤ δ) (hpoint : ∀ i, |w i| ≤ δ) :
    ‖realSummableDiagonalOperator w habs‖ ≤ δ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro f
  have hsumf : Summable fun i => ‖f i‖ ^ 2 :=
    HilbertSchmidt.summable_coe_sq f
  have hsumT : Summable fun i =>
      ‖(realSummableDiagonalOperator w habs f) i‖ ^ 2 :=
    HilbertSchmidt.summable_coe_sq
      (realSummableDiagonalOperator w habs f)
  have hterm : ∀ i,
      ‖(realSummableDiagonalOperator w habs f) i‖ ^ 2 ≤
        δ ^ 2 * ‖f i‖ ^ 2 := by
    intro i
    rw [realSummableDiagonalOperator_apply, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (abs_nonneg (w i)) hδ).2 (hpoint i))
      (sq_nonneg ‖f i‖)
  have hpow : ‖realSummableDiagonalOperator w habs f‖ ^ 2 ≤
      (δ * ‖f‖) ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, mul_pow,
      HilbertSchmidt.lp_norm_sq_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumT
      (hsumf.mul_left (δ ^ 2))
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hδ (norm_nonneg f))).1 hpow

/-- Adding an absolutely summable real diagonal does not change the maximal
domain of an arbitrary, possibly unbounded, real diagonal Hamiltonian. -/
theorem maximalRealDiagonalDomain_add_summable_eq
    {I : Type*} (energy w : I → ℝ)
    (habs : Summable (fun i => |w i|)) :
    RHTower.maximalRealDiagonalDomain (fun i => energy i + w i) =
      RHTower.maximalRealDiagonalDomain energy := by
  ext x
  constructor
  · intro htotal
    change Memℓp
      (fun i => ((energy i + w i : ℝ) : ℂ) * x i) 2 at htotal
    have hw : Memℓp (fun i => (w i : ℂ) * x i) 2 := by
      have hop := lp.memℓp (realSummableDiagonalOperator w habs x)
      rw [show (fun i => (w i : ℂ) * x i) =
          fun i => (realSummableDiagonalOperator w habs x) i by
        funext i
        rw [realSummableDiagonalOperator_apply]]
      exact hop
    have hsub := htotal.sub hw
    change Memℓp (fun i => (energy i : ℂ) * x i) 2
    have hfun : (fun i => (energy i : ℂ) * x i) =
        (fun i => ((energy i + w i : ℝ) : ℂ) * x i) -
          fun i => (w i : ℂ) * x i := by
      funext i
      change (energy i : ℂ) * x i =
        ((energy i + w i : ℝ) : ℂ) * x i -
          (w i : ℂ) * x i
      push_cast
      ring
    rw [hfun]
    exact hsub
  · intro henergy
    change Memℓp (fun i => (energy i : ℂ) * x i) 2 at henergy
    have hw : Memℓp (fun i => (w i : ℂ) * x i) 2 := by
      have hop := lp.memℓp (realSummableDiagonalOperator w habs x)
      rw [show (fun i => (w i : ℂ) * x i) =
          fun i => (realSummableDiagonalOperator w habs x) i by
        funext i
        rw [realSummableDiagonalOperator_apply]]
      exact hop
    have hadd := henergy.add hw
    change Memℓp
      (fun i => ((energy i + w i : ℝ) : ℂ) * x i) 2
    have hfun :
        (fun i => ((energy i + w i : ℝ) : ℂ) * x i) =
          (fun i => (energy i : ℂ) * x i) +
            fun i => (w i : ℂ) * x i := by
      funext i
      change ((energy i + w i : ℝ) : ℂ) * x i =
        (energy i : ℂ) * x i + (w i : ℂ) * x i
      push_cast
      ring
    rw [hfun]
    exact hadd

/-- On the common maximal domain, the coupled Hamiltonian is exactly the
uncoupled Hamiltonian plus the bounded interaction operator. -/
theorem maximalRealDiagonal_add_summable_apply
    {I : Type*} (energy w : I → ℝ)
    (habs : Summable (fun i => |w i|))
    (x : (RHTower.maximalRealDiagonal
      (fun i => energy i + w i)).domain) :
    RHTower.maximalRealDiagonal (fun i => energy i + w i) x =
      RHTower.maximalRealDiagonal energy
        ⟨x, by
          change (x : RHTower.DiagonalL2 I) ∈
            RHTower.maximalRealDiagonalDomain energy
          rw [← maximalRealDiagonalDomain_add_summable_eq
            energy w habs]
          exact x.property⟩ +
        realSummableDiagonalOperator w habs x := by
  apply lp.ext
  funext i
  change ((energy i + w i : ℝ) : ℂ) *
      (x : RHTower.DiagonalL2 I) i =
    (energy i : ℂ) * (x : RHTower.DiagonalL2 I) i +
      (realSummableDiagonalOperator w habs x) i
  rw [realSummableDiagonalOperator_apply]
  push_cast
  ring

/-- The Hamiltonian obtained by an absolutely summable real diagonal
perturbation is self-adjoint on the unchanged maximal domain. -/
theorem maximalRealDiagonal_add_summable_isSelfAdjoint
    {I : Type*} (energy w : I → ℝ) :
    IsSelfAdjoint
      (RHTower.maximalRealDiagonal (fun i => energy i + w i)) := by
  classical
  exact RHTower.maximalRealDiagonal_isSelfAdjoint _

/-- On a finite label set, finite-support maximal projective freedom is
exactly the existing all-order maximal-projectivity condition. -/
theorem finitelySupportedMaximallyProjectiveEnergy_iff
    {I : Type*} [Fintype I] (energy : I → ℝ) :
    FinitelySupportedMaximallyProjectiveEnergy energy ↔
      MaximallyProjectiveEnergy energy := by
  classical
  constructor
  · intro hmax k hbalanced hzero
    let raw : I →₀ ℤ := Finsupp.equivFunOnFinite.symm k
    have hcharge : integerCharacterCharge I raw = 0 := by
      change raw.sum (fun _ m => m) = 0
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simpa [raw, SpectralCharacterBalanced] using hbalanced
    let K : ProjectiveCharacter I := ⟨raw, hcharge⟩
    have hKzero : K = 0 := by
      apply hmax K
      change raw.sum (fun i m => (m : ℝ) * energy i) = 0
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      simpa [raw] using hzero
    funext i
    have hi :=
      congrArg (fun q : ProjectiveCharacter I => q.1 i) hKzero
    simpa [K, raw] using hi
  · intro hmax K hzero
    let k : I → ℤ := fun i => K.1 i
    have hbalanced : SpectralCharacterBalanced k := by
      unfold SpectralCharacterBalanced
      have hcharge := K.2
      change K.1.sum (fun _ m => m) = 0 at hcharge
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hcharge
      simpa [k] using hcharge
    have henergy : (∑ i, (k i : ℝ) * energy i) = 0 := by
      change (∑ i, (K.1 i : ℝ) * energy i) = 0
      rw [← Finsupp.sum_fintype K.1
        (fun i m => (m : ℝ) * energy i) (fun _ => by simp)]
      exact hzero
    have hkzero := hmax k hbalanced henergy
    apply Subtype.ext
    ext i
    exact congrFun hkzero i

/-- One saturated infinite spectrum forces the all-order permutation floor
on every embedded positive-weight finite window. -/
theorem
    FinitelySupportedMaximallyProjectiveEnergy.all_finiteWindow_collisionFloor
    {I J : Type*} [Fintype J] [DecidableEq J]
    {energy : I → ℝ}
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy)
    (e : J ↪ I) {weight : J → ℝ}
    (hweight : ∀ j, 0 < weight j) :
    ∀ n : ℕ,
      fidelityReplicaCollisionMass weight (energy ∘ e) n =
        fidelityReplicaPermutationFloor weight n := by
  exact
    (all_fidelityReplicaCollisionMass_eq_floor_iff
      hweight (energy ∘ e)).2
      ((finitelySupportedMaximallyProjectiveEnergy_iff
        (energy ∘ e)).1 (hmax.comp_embedding e))

/-- **Countable operator-norm weak-interaction saturation.**  For every
pair of countable spectra and every positive operator-norm budget, one
separable absolutely summable interaction simultaneously:

* lies strictly inside the budget pointwise and in operator norm;
* defines a bounded self-adjoint Schatten-1 perturbation on `ℓ²(A × B)`;
* erases every nonzero finitely supported projective relation.

Thus every finite window of this single infinite perturbed spectrum reaches
the permutation collision floor at every replica order. -/
theorem exists_arbitrarilyWeak_traceClassSeparableInteraction_saturating
    {A B : Type*} [Countable A] [Countable B]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (u : A → ℝ) (v : B → ℝ),
      ∃ hw : Summable (fun x : A × B => |u x.1 * v x.2|),
        Summable (fun i => |u i|) ∧
        Summable (fun j => |v j|) ∧
        (∀ x : A × B, |u x.1 * v x.2| < δ) ∧
        ‖realSummableDiagonalOperator
          (fun x : A × B => u x.1 * v x.2) hw‖ < δ ∧
        IsSelfAdjoint
          (realSummableDiagonalOperator
            (fun x : A × B => u x.1 * v x.2) hw) ∧
        RHTower.MemSchattenClass 1
          (realSummableDiagonalOperator
            (fun x : A × B => u x.1 * v x.2) hw) ∧
        FinitelySupportedMaximallyProjectiveEnergy
          (fun x : A × B =>
            left x.1 + right x.2 + u x.1 * v x.2) := by
  classical
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨u, v, hu, hv, hw, hsmall, hmax⟩ :=
    exists_smallSeparableInteraction_finitelySupportedMaximallyProjective
      left right (δ / 2) hhalf
  refine ⟨u, v, hw, hu, hv, ?_, ?_, ?_, ?_, hmax⟩
  · intro x
    exact lt_trans (hsmall x) (by linarith)
  · exact lt_of_le_of_lt
      (norm_realSummableDiagonalOperator_le _ hw (δ / 2)
        hhalf.le (fun x => (hsmall x).le)) (by linarith)
  · exact realSummableDiagonalOperator_isSelfAdjoint _ hw
  · exact realSummableDiagonalOperator_memSchattenClass_one _ hw

/-- **Unbounded-Hamiltonian form of countable weak-interaction
saturation.**  The saturating perturbation applies to arbitrary countable
real spectra, even when the uncoupled Hamiltonian is unbounded.  The
coupled Hamiltonian is self-adjoint, has exactly the same maximal domain,
and differs there by an arbitrarily small bounded self-adjoint Schatten-1
separable interaction. -/
theorem
    exists_arbitrarilyWeak_traceClassSeparableHamiltonian_saturating
    {A B : Type*} [Countable A] [Countable B]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (u : A → ℝ) (v : B → ℝ),
      ∃ hw : Summable (fun x : A × B => |u x.1 * v x.2|),
        Summable (fun i => |u i|) ∧
        Summable (fun j => |v j|) ∧
        (∀ x : A × B, |u x.1 * v x.2| < δ) ∧
        ‖realSummableDiagonalOperator
          (fun x : A × B => u x.1 * v x.2) hw‖ < δ ∧
        IsSelfAdjoint
          (realSummableDiagonalOperator
            (fun x : A × B => u x.1 * v x.2) hw) ∧
        RHTower.MemSchattenClass 1
          (realSummableDiagonalOperator
            (fun x : A × B => u x.1 * v x.2) hw) ∧
        RHTower.maximalRealDiagonalDomain
            (fun x : A × B =>
              left x.1 + right x.2 + u x.1 * v x.2) =
          RHTower.maximalRealDiagonalDomain
            (fun x : A × B => left x.1 + right x.2) ∧
        IsSelfAdjoint
          (RHTower.maximalRealDiagonal
            (fun x : A × B =>
              left x.1 + right x.2 + u x.1 * v x.2)) ∧
        FinitelySupportedMaximallyProjectiveEnergy
          (fun x : A × B =>
            left x.1 + right x.2 + u x.1 * v x.2) := by
  classical
  obtain ⟨u, v, hw, hu, hv, hsmall, hnorm, hself,
      htrace, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassSeparableInteraction_saturating
      left right δ hδ
  refine ⟨u, v, hw, hu, hv, hsmall, hnorm, hself, htrace,
    ?_, ?_, hmax⟩
  · exact maximalRealDiagonalDomain_add_summable_eq
      (fun x : A × B => left x.1 + right x.2)
      (fun x : A × B => u x.1 * v x.2) hw
  · exact RHTower.maximalRealDiagonal_isSelfAdjoint _

/-- **Universal countable pure-point instability law.**  Every countable
real spectrum, with no boundedness, simplicity, or arithmetic assumption,
admits an arbitrarily small absolutely summable diagonal perturbation whose
bounded operator is self-adjoint and Schatten-1, whose perturbed maximal
Hamiltonian is self-adjoint on exactly the original domain, and whose
spectrum has no nonzero finitely supported projective relation.

This is the structure-free form of the law.  The preceding separable
theorem strengthens it for composite spectra by forcing the perturbation to
factor through the two subsystems. -/
theorem exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
    {I : Type*} [Countable I]
    (energy : I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      (∀ i, |w i| < δ) ∧
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      IsSelfAdjoint (realSummableDiagonalOperator w hw) ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      IsSelfAdjoint
        (RHTower.maximalRealDiagonal (fun i => energy i + w i)) ∧
      FinitelySupportedMaximallyProjectiveEnergy
        (fun i => energy i + w i) := by
  classical
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨u, v, hu, hv, hprod, hsmall, hmax⟩ :=
    exists_smallSeparableInteraction_finitelySupportedMaximallyProjective
      energy (fun _ : Unit => 0) (δ / 2) hhalf
  let e : I ↪ I × Unit :=
    ⟨fun i => (i, ()), fun _ _ h => Prod.mk.inj h |>.1⟩
  let w : I → ℝ := fun i => u i * v ()
  have hw : Summable (fun i => |w i|) := by
    have h := hprod.comp_injective e.injective
    change Summable (fun i => |u i * v ()|) at h
    simpa [w] using h
  have hpoint : ∀ i, |w i| < δ / 2 := by
    intro i
    simpa [w] using hsmall (i, ())
  have hmaxI : FinitelySupportedMaximallyProjectiveEnergy
      (fun i => energy i + w i) := by
    have hrestrict := hmax.comp_embedding e
    change FinitelySupportedMaximallyProjectiveEnergy
      (fun i => energy i + 0 + u i * v ()) at hrestrict
    simpa [w] using hrestrict
  refine ⟨w, hw, ?_, ?_, ?_, ?_, ?_, ?_, hmaxI⟩
  · intro i
    exact lt_trans (hpoint i) (by linarith)
  · exact lt_of_le_of_lt
      (norm_realSummableDiagonalOperator_le w hw (δ / 2)
        hhalf.le (fun i => (hpoint i).le)) (by linarith)
  · exact realSummableDiagonalOperator_isSelfAdjoint w hw
  · exact realSummableDiagonalOperator_memSchattenClass_one w hw
  · exact maximalRealDiagonalDomain_add_summable_eq energy w hw
  · exact RHTower.maximalRealDiagonal_isSelfAdjoint _

/-- Existence of an exact nonzero finite projective recurrence constraint. -/
def HasNontrivialFinitelySupportedProjectiveRelation
    {I : Type*} (energy : I → ℝ) : Prop :=
  ∃ k : ProjectiveCharacter I, k ≠ 0 ∧
    (∑ i ∈ k.1.support, (k.1 i : ℝ) * energy i) = 0

/-- A saturated spectrum has no nontrivial finite projective recurrence
constraint. -/
theorem
    not_hasNontrivialFinitelySupportedProjectiveRelation_of_saturating
    {I : Type*} {energy : I → ℝ}
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy) :
    ¬ HasNontrivialFinitelySupportedProjectiveRelation energy := by
  rintro ⟨k, hk, hzero⟩
  exact hk (hmax k hzero)

/-- **No positive recurrence-constraint stability radius.**  Around every
countable pure-point Hamiltonian, every positive operator-norm ball of
absolutely summable self-adjoint diagonal perturbations contains a
domain-preserving Schatten-1 perturbation that destroys all exact nonzero
finite projective constraints simultaneously. -/
theorem no_positive_projectiveRelation_traceClass_stabilityRadius
    {I : Type*} [Countable I] (energy : I → ℝ) :
    ¬ ∃ δ : ℝ, 0 < δ ∧
      ∀ (w : I → ℝ) (hw : Summable (fun i => |w i|)),
        ‖realSummableDiagonalOperator w hw‖ < δ →
          HasNontrivialFinitelySupportedProjectiveRelation
            (fun i => energy i + w i) := by
  rintro ⟨δ, hδ, hstable⟩
  obtain ⟨w, hw, _, hnorm, _, _, _, _, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  exact
    (not_hasNontrivialFinitelySupportedProjectiveRelation_of_saturating
      hmax) (hstable w hw hnorm)

/-- Every failure of maximal projective freedom is detected by a strict
excess above the permutation floor at some finite replica order. -/
theorem exists_replicaCollisionMass_strictlyAboveFloor_of_not_maximal
    {J : Type*} [Fintype J] [DecidableEq J]
    {weight : J → ℝ} (hweight : ∀ j, 0 < weight j)
    {energy : J → ℝ}
    (hnot : ¬ MaximallyProjectiveEnergy energy) :
    ∃ n : ℕ,
      fidelityReplicaPermutationFloor weight n <
        fidelityReplicaCollisionMass weight energy n := by
  have hnotall : ¬ ∀ n : ℕ,
      fidelityReplicaCollisionMass weight energy n =
        fidelityReplicaPermutationFloor weight n := by
    intro hall
    exact hnot
      ((all_fidelityReplicaCollisionMass_eq_floor_iff
        hweight energy).1 hall)
  push Not at hnotall
  obtain ⟨n, hne⟩ := hnotall
  exact ⟨n, lt_of_le_of_ne
    (fidelityReplicaCollisionMass_floor_le hweight energy n)
      hne.symm⟩

/-- **Countable recurrence wall crossing.**  If one finite window of a
countable pure-point Hamiltonian carries an exact recurrence relation, then
inside every positive operator-norm budget there is a domain-preserving
Schatten-1 perturbation for which every replica order of that same window
reaches the permutation floor.  At some finite replica order the
infinite-time collision statistic drops strictly, however small the
perturbation. -/
theorem exists_arbitrarilyWeak_countableReplicaWallCrossing
    {I J : Type*} [Countable I] [Fintype J] [DecidableEq J]
    (energy : I → ℝ) (e : J ↪ I)
    {weight : J → ℝ} (hweight : ∀ j, 0 < weight j)
    (hresonant : ¬ MaximallyProjectiveEnergy (energy ∘ e))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      (∀ n : ℕ,
        fidelityReplicaCollisionMass weight
            ((fun i => energy i + w i) ∘ e) n =
          fidelityReplicaPermutationFloor weight n) ∧
      ∃ n : ℕ,
        fidelityReplicaCollisionMass weight (energy ∘ e) n >
          fidelityReplicaCollisionMass weight
            ((fun i => energy i + w i) ∘ e) n := by
  obtain ⟨w, hw, _, hnorm, _, htrace, hdomain, _, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  have hafter : ∀ n : ℕ,
      fidelityReplicaCollisionMass weight
          ((fun i => energy i + w i) ∘ e) n =
        fidelityReplicaPermutationFloor weight n :=
    hmax.all_finiteWindow_collisionFloor e hweight
  obtain ⟨n, hbefore⟩ :=
    exists_replicaCollisionMass_strictlyAboveFloor_of_not_maximal
      hweight hresonant
  refine ⟨w, hw, hnorm, htrace, hdomain, hafter, n, ?_⟩
  rw [hafter n]
  exact hbefore

end

end GaloisForLFunctions.HTGeometry
