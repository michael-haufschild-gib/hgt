import GaloisForLFunctions.RHTower.CCMMetaplecticOscillatorTriple
import GaloisForLFunctions.RHTower.HermiteL2ClosedSpan
import GaloisForLFunctions.RHTower.CCMMetaplecticGammaMomentDeterminacy
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiOrthonormal

/-!
# The metaplectic Jacobi data are the even metaplectic representation

Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, Theorem 5.2(iv).

On finitely supported sequences let `J` be the Jacobi operator with zero diagonal and the
metaplectic off-diagonal coefficients `a_n = √((2n+1)(2n+2))/2` (forced by the `sl₂` relation,
`CCMMetaplecticJacobiRigidity`), `N e_n = n e_n`, and `C = [J, N]`.

* `J`, `N` realize the formal CCM actions `ccmCyclicJacobiAction`, `ccmCyclicNumberAction`;
  hence `[C, N] = J` and `[J, C] = -(4N + 1)`, and
  `(2N + 1/2, (J - C)/2, -(J + C)/2)` is an `sl₂`-triple.
* The even Hermite synthesis `Φ e_n = ĥ_{2n}` intertwines `J` with `i(E + F)`, `N` with
  `(i/2)(E - F) - 1/4` and `C` with `H = x∂ + 1/2`, so it carries the CCM triple onto the Cayley
  transform `(i(E - F), (i(E + F) - H)/2, -(i(E + F) + H)/2)` of the oscillator triple
  `(H, E, F)`: the even part of the metaplectic representation.
* `Φ` extends to the unitary `ℓ²(ℕ) ≃ L²(ℝ)^ev`, `e_n ↦ ĥ_{2n}`, given by the even Hermite Hilbert
  basis.
* The spectral moments `⟨e_0, J^k e_0⟩` are the moments of the normalized Gamma measure
  `|Γ(1/4 + is/2)|² ds`, which they determine uniquely
  (`CCMMetaplecticGammaMomentDeterminacy`).
-/

noncomputable section

open Complex MeasureTheory GaloisForLFunctions
open scoped SchwartzMap Real

namespace RHTower

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The CCM operators on finitely supported sequences -/

/-- The metaplectic Jacobi coefficients `a_n = √((2n+1)(2n+2))/2`. -/
def ccmMetaplecticCoeff (n : ℕ) : ℂ := ((ccmMetaplecticJacobiCoefficient n : ℝ) : ℂ)

theorem star_ccmMetaplecticCoeff (n : ℕ) : star (ccmMetaplecticCoeff n) = ccmMetaplecticCoeff n :=
  Complex.conj_ofReal _

theorem ccmMetaplecticCoeff_mul_self (n : ℕ) :
    ccmMetaplecticCoeff n * ccmMetaplecticCoeff n = ((n : ℂ) + 1 / 2) * ((n : ℂ) + 1) := by
  rw [ccmMetaplecticCoeff, ← Complex.ofReal_mul, ← pow_two, ccmMetaplecticJacobiCoefficient_sq]
  push_cast
  ring

/-- Lower part `a_{n-1} e_{n-1}` of the `n`-th Jacobi column. -/
def ccmMetaplecticLowerColumn : ℕ → (ℕ →₀ ℂ)
  | 0 => 0
  | m + 1 => Finsupp.single m (ccmMetaplecticCoeff m)

/-- Column `J e_n = a_{n-1} e_{n-1} + a_n e_{n+1}` of the metaplectic Jacobi matrix. -/
def ccmMetaplecticJacobiColumn (n : ℕ) : ℕ →₀ ℂ :=
  ccmMetaplecticLowerColumn n + Finsupp.single (n + 1) (ccmMetaplecticCoeff n)

/-- The CCM Jacobi operator `J` on finitely supported sequences. -/
def ccmMetaplecticJacobiFin : Module.End ℂ (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ ccmMetaplecticJacobiColumn

/-- The number operator `N e_n = n e_n`. -/
def ccmNumberFin : Module.End ℂ (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun n => Finsupp.single n (n : ℂ)

theorem ccmMetaplecticJacobiFin_single (n : ℕ) (c : ℂ) :
    ccmMetaplecticJacobiFin (Finsupp.single n c) = c • ccmMetaplecticJacobiColumn n := by
  simp [ccmMetaplecticJacobiFin, Finsupp.linearCombination_single]

theorem ccmNumberFin_single (n : ℕ) (c : ℂ) :
    ccmNumberFin (Finsupp.single n c) = Finsupp.single n ((n : ℂ) * c) := by
  simp [ccmNumberFin, Finsupp.linearCombination_single, Finsupp.smul_single, mul_comm]

/-- An operator on finitely supported sequences realizes a formal pointwise action. -/
def CCMRealizes (T : Module.End ℂ (ℕ →₀ ℂ)) (F : (ℕ → ℂ) → ℕ → ℂ) : Prop :=
  ∀ (x : ℕ →₀ ℂ) (m : ℕ), T x m = F x m

theorem ccmCyclicJacobiAction_add (a x y : ℕ → ℂ) (m : ℕ) :
    ccmCyclicJacobiAction a (x + y) m = ccmCyclicJacobiAction a x m + ccmCyclicJacobiAction a y m := by
  unfold ccmCyclicJacobiAction
  split_ifs <;> simp only [Pi.add_apply] <;> ring

theorem ccmMetaplecticJacobiColumn_apply (n m : ℕ) :
    ccmMetaplecticJacobiColumn n m =
      (if m + 1 = n then ccmMetaplecticCoeff m else 0) +
        (if n + 1 = m then ccmMetaplecticCoeff n else 0) := by
  unfold ccmMetaplecticJacobiColumn
  rw [Finsupp.add_apply, Finsupp.single_apply]
  congr 1
  rcases n with _ | j
  · simp [ccmMetaplecticLowerColumn]
  · simp only [ccmMetaplecticLowerColumn, Finsupp.single_apply]
    by_cases h : j = m
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (by omega))]

/-- `J` realizes `ccmCyclicJacobiAction` with the metaplectic coefficients. -/
theorem ccmMetaplecticJacobiFin_realizes :
    CCMRealizes ccmMetaplecticJacobiFin (ccmCyclicJacobiAction ccmMetaplecticCoeff) := by
  intro x m
  induction x using Finsupp.induction_linear with
  | zero => simp [ccmCyclicJacobiAction]
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.coe_add, ccmCyclicJacobiAction_add]
  | single n c =>
    rw [ccmMetaplecticJacobiFin_single, Finsupp.smul_apply, smul_eq_mul,
      ccmMetaplecticJacobiColumn_apply]
    rcases m with _ | m
    · simp only [ccmCyclicJacobiAction, if_true, Finsupp.single_apply]
      by_cases h : n = 1
      · subst h; simp [mul_comm]
      · rw [if_neg (fun h' => h h'.symm), if_neg h]
        simp
    · simp only [ccmCyclicJacobiAction, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
        Finsupp.single_apply, star_ccmMetaplecticCoeff]
      by_cases h1 : n = m
      · subst h1
        rw [if_neg (by omega), if_pos rfl, if_pos rfl, if_neg (by omega)]
        ring
      · by_cases h2 : n = m + 2
        · subst h2
          rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl]
          ring
        · rw [if_neg (fun h => h2 h.symm), if_neg (fun h => h1 (by omega)), if_neg h1,
            if_neg h2]
          ring

/-- `N` realizes `ccmCyclicNumberAction`. -/
theorem ccmNumberFin_realizes : CCMRealizes ccmNumberFin ccmCyclicNumberAction := by
  intro x m
  induction x using Finsupp.induction_linear with
  | zero => simp [ccmCyclicNumberAction]
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy]
    simp only [ccmCyclicNumberAction, Finsupp.coe_add, Pi.add_apply]
    ring
  | single n c =>
    rw [ccmNumberFin_single]
    simp only [ccmCyclicNumberAction, Finsupp.single_apply]
    split_ifs with h
    · subst h; rfl
    · simp

/-- Commutators realize formal commutators. -/
theorem ccmRealizes_lie {S T : Module.End ℂ (ℕ →₀ ℂ)} {F G : (ℕ → ℂ) → ℕ → ℂ}
    (hS : CCMRealizes S F) (hT : CCMRealizes T G) :
    CCMRealizes ⁅S, T⁆ (ccmFormalCommutator F G) := by
  intro x m
  have hTx : ⇑(T x) = G x := funext (hT x)
  have hSx : ⇑(S x) = F x := funext (hS x)
  change (S * T - T * S) x m = _
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Finsupp.sub_apply, hS, hT, hTx, hSx]
  rfl

theorem ccmRealizes_ext {S T : Module.End ℂ (ℕ →₀ ℂ)} {F : (ℕ → ℂ) → ℕ → ℂ}
    (hS : CCMRealizes S F) (hT : CCMRealizes T F) : S = T :=
  LinearMap.ext fun x => Finsupp.ext fun m => (hS x m).trans (hT x m).symm

/-- `[C, N] = J` with `C = [J, N]` (Connes--Consani Lemma (47)(i)). -/
theorem ccmMetaplectic_lie_commutator_number :
    ⁅⁅ccmMetaplecticJacobiFin, ccmNumberFin⁆, ccmNumberFin⁆ = ccmMetaplecticJacobiFin := by
  apply ccmRealizes_ext
    (ccmRealizes_lie (ccmRealizes_lie ccmMetaplecticJacobiFin_realizes ccmNumberFin_realizes)
      ccmNumberFin_realizes)
  intro x m
  rw [ccmCyclicJacobi_double_number_commutator, ← ccmMetaplecticJacobiFin_realizes]

/-- `[J, C] = -(4N + 1)` exactly for the metaplectic coefficients
(Connes--Consani Lemma (47)(iii)). -/
theorem ccmMetaplectic_lie_jacobi_commutator :
    ⁅ccmMetaplecticJacobiFin, ⁅ccmMetaplecticJacobiFin, ccmNumberFin⁆⁆ =
      -((4 : ℂ) • ccmNumberFin + 1) := by
  apply ccmRealizes_ext
    (ccmRealizes_lie ccmMetaplecticJacobiFin_realizes
      (ccmRealizes_lie ccmMetaplecticJacobiFin_realizes ccmNumberFin_realizes))
  intro x m
  rw [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Finsupp.neg_apply, Finsupp.add_apply, Finsupp.smul_apply, ccmNumberFin_realizes, smul_eq_mul]
  rcases m with _ | m
  · rw [ccmCyclicJacobi_double_commutator_zero, star_ccmMetaplecticCoeff,
      ccmMetaplecticCoeff_mul_self]
    simp only [ccmCyclicNumberAction]
    push_cast
    ring
  · rw [ccmCyclicJacobi_double_commutator_succ, star_ccmMetaplecticCoeff,
      star_ccmMetaplecticCoeff, ccmMetaplecticCoeff_mul_self, ccmMetaplecticCoeff_mul_self]
    simp only [ccmCyclicNumberAction]
    push_cast
    ring

/-- The CCM element `h = 2N + 1/2`. -/
def ccmMetaplecticTripleH : Module.End ℂ (ℕ →₀ ℂ) := (2 : ℂ) • ccmNumberFin + (2⁻¹ : ℂ) • 1

/-- The CCM element `e = (J - C)/2`. -/
def ccmMetaplecticTripleE : Module.End ℂ (ℕ →₀ ℂ) :=
  (2⁻¹ : ℂ) • (ccmMetaplecticJacobiFin - ⁅ccmMetaplecticJacobiFin, ccmNumberFin⁆)

/-- The CCM element `f = -(J + C)/2`. -/
def ccmMetaplecticTripleF : Module.End ℂ (ℕ →₀ ℂ) :=
  -((2⁻¹ : ℂ) • (ccmMetaplecticJacobiFin + ⁅ccmMetaplecticJacobiFin, ccmNumberFin⁆))

theorem ccmLie_one_left {A : Type*} [Ring A] (x : A) : ⁅(1 : A), x⁆ = 0 := by
  change 1 * x - x * 1 = 0
  rw [mul_one, one_mul, sub_self]

/-- `sl₂` from Jacobi-type relations.  If `Z` is central, `[[J,N],N] = J` and
`[J,[J,N]] = -(4N + Z)`, then `(2N + Z/2, (J - [J,N])/2, -(J + [J,N])/2)` satisfies the
`sl₂` relations. -/
theorem ccmSl2_of_jacobi_relations {L : Type*} [LieRing L] [LieAlgebra ℂ L] (J N Z : L)
    (hZ : ∀ X : L, ⁅Z, X⁆ = 0) (hCN : ⁅⁅J, N⁆, N⁆ = J)
    (hJC : ⁅J, ⁅J, N⁆⁆ = -((4 : ℂ) • N + Z)) (hne : (2 : ℂ) • N + (2⁻¹ : ℂ) • Z ≠ 0) :
    IsSl2Triple ((2 : ℂ) • N + (2⁻¹ : ℂ) • Z) ((2⁻¹ : ℂ) • (J - ⁅J, N⁆))
      (-((2⁻¹ : ℂ) • (J + ⁅J, N⁆))) := by
  have hNC : ⁅N, ⁅J, N⁆⁆ = -J := by rw [← lie_skew, hCN]
  have hNJ : ⁅N, J⁆ = -⁅J, N⁆ := by rw [← lie_skew]
  have hCJ : ⁅⁅J, N⁆, J⁆ = (4 : ℂ) • N + Z := by rw [← lie_skew, hJC, neg_neg]
  refine ⟨hne, ?_, ?_, ?_⟩
  · simp only [lie_smul, smul_lie, lie_neg, lie_add, sub_lie, lie_self, hJC, hCJ]
    module
  · simp only [lie_smul, smul_lie, add_lie, lie_sub, hZ, hNJ, hNC]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    module
  · simp only [lie_smul, smul_lie, lie_neg, lie_add, add_lie, hZ, hNJ, hNC]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    module

/-- **The CCM `sl₂`-triple** built from the forced metaplectic Jacobi coefficients. -/
theorem ccmMetaplectic_isSl2Triple :
    IsSl2Triple ccmMetaplecticTripleH ccmMetaplecticTripleE ccmMetaplecticTripleF := by
  refine ccmSl2_of_jacobi_relations ccmMetaplecticJacobiFin ccmNumberFin 1 (fun X => ccmLie_one_left X)
    ccmMetaplectic_lie_commutator_number ccmMetaplectic_lie_jacobi_commutator ?_
  intro h
  have h0 := congrArg (fun T : Module.End ℂ (ℕ →₀ ℂ) => T (Finsupp.single 0 1) 0) h
  simp [ccmNumberFin_single] at h0

/-! ## The Cayley transform of the oscillator triple -/

/-- **Cayley transform.**  If `(H, E, F)` is an `sl₂`-triple over `ℂ`, so is
`(i(E - F), (i(E + F) - H)/2, -(i(E + F) + H)/2)`. -/
theorem ccmCayley_isSl2Triple {L : Type*} [LieRing L] [LieAlgebra ℂ L] {H E F : L}
    (t : IsSl2Triple H E F) :
    IsSl2Triple (I • (E - F)) ((2⁻¹ : ℂ) • (I • (E + F) - H))
      (-((2⁻¹ : ℂ) • (I • (E + F) + H))) := by
  have hEF := t.lie_e_f
  have hHE := t.lie_h_e_nsmul
  have hHF := t.lie_h_f_nsmul
  have hEH : ⁅E, H⁆ = -(2 • E) := by rw [← lie_skew, hHE]
  have hFH : ⁅F, H⁆ = 2 • F := by rw [← lie_skew, hHF, neg_neg]
  have hFE : ⁅F, E⁆ = -H := by rw [← lie_skew, hEF]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hE : E = F := by
      have := (smul_eq_zero.mp h).resolve_left I_ne_zero
      exact sub_eq_zero.mp this
    apply t.h_ne_zero
    rw [← hEF, hE, lie_self]
  · simp only [lie_smul, smul_lie, lie_neg, lie_add, add_lie, sub_lie, lie_self, hEF, hFE, hEH,
      hFH, hHE, hHF]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
    match_scalars <;> ring_nf
  · simp only [lie_smul, smul_lie, lie_add, lie_sub, sub_lie, lie_self, hEF, hFE, hEH, hFH]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
    match_scalars
    all_goals ring_nf
    all_goals simp [I_sq]
  · simp only [lie_smul, smul_lie, lie_neg, lie_add, sub_lie, lie_self, hEF, hFE, hEH, hFH]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
    match_scalars
    all_goals ring_nf
    all_goals simp [I_sq]

/-- The even metaplectic triple `(i(E - F), (i(E + F) - H)/2, -(i(E + F) + H)/2)` on `𝓢(ℝ, ℂ)`. -/
theorem ccmOscillatorCayley_isSl2Triple :
    IsSl2Triple (I • (ccmOscillatorE - ccmOscillatorF))
      ((2⁻¹ : ℂ) • (I • (ccmOscillatorE + ccmOscillatorF) - ccmOscillatorH))
      (-((2⁻¹ : ℂ) • (I • (ccmOscillatorE + ccmOscillatorF) + ccmOscillatorH))) :=
  ccmCayley_isSl2Triple ccmOscillator_isSl2Triple

/-! ## The even Hermite synthesis intertwines the two triples -/

/-- Even Hermite synthesis `Φ e_n = ĥ_{2n}`. -/
def ccmEvenHermiteSynthesis : (ℕ →₀ ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  Finsupp.linearCombination ℂ fun n => ccmHermiteUnit (2 * n)

/-- `Φ` intertwines `S` with the Schwartz operator `S'`. -/
def CCMIntertwines (S : Module.End ℂ (ℕ →₀ ℂ)) (S' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) : Prop :=
  ∀ x : ℕ →₀ ℂ, S' (ccmEvenHermiteSynthesis x) = ccmEvenHermiteSynthesis (S x)

theorem ccmIntertwines_add {S T : Module.End ℂ (ℕ →₀ ℂ)} {S' T' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hS : CCMIntertwines S S') (hT : CCMIntertwines T T') : CCMIntertwines (S + T) (S' + T') :=
  fun x => by rw [add_apply, hS, hT, LinearMap.add_apply, map_add]

theorem ccmIntertwines_sub {S T : Module.End ℂ (ℕ →₀ ℂ)} {S' T' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hS : CCMIntertwines S S') (hT : CCMIntertwines T T') : CCMIntertwines (S - T) (S' - T') :=
  fun x => by rw [sub_apply, hS, hT, LinearMap.sub_apply, map_sub]

theorem ccmIntertwines_neg {S : Module.End ℂ (ℕ →₀ ℂ)} {S' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hS : CCMIntertwines S S') : CCMIntertwines (-S) (-S') :=
  fun x => by rw [neg_apply, hS, LinearMap.neg_apply, map_neg]

theorem ccmIntertwines_smul {S : Module.End ℂ (ℕ →₀ ℂ)} {S' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (c : ℂ)
    (hS : CCMIntertwines S S') : CCMIntertwines (c • S) (c • S') :=
  fun x => by rw [smul_apply, hS, LinearMap.smul_apply, map_smul]

theorem ccmIntertwines_one : CCMIntertwines 1 1 := fun _ => rfl

theorem ccmIntertwines_mul {S T : Module.End ℂ (ℕ →₀ ℂ)} {S' T' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hS : CCMIntertwines S S') (hT : CCMIntertwines T T') : CCMIntertwines (S * T) (S' * T') :=
  fun x => by rw [mul_apply_eq_comp, hT, hS, Module.End.mul_apply]

theorem ccmIntertwines_lie {S T : Module.End ℂ (ℕ →₀ ℂ)} {S' T' : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hS : CCMIntertwines S S') (hT : CCMIntertwines T T') : CCMIntertwines ⁅S, T⁆ ⁅S', T'⁆ := by
  rw [Ring.lie_def]
  change CCMIntertwines (S * T - T * S) (S' * T' - T' * S')
  exact ccmIntertwines_sub (ccmIntertwines_mul hS hT) (ccmIntertwines_mul hT hS)

theorem ccmEvenHermiteSynthesis_single (n : ℕ) (c : ℂ) :
    ccmEvenHermiteSynthesis (Finsupp.single n c) = c • ccmHermiteUnit (2 * n) := by
  simp [ccmEvenHermiteSynthesis, Finsupp.linearCombination_single]

/-- `Φ` intertwines the CCM Jacobi operator with `J = i(E + F) = πx² + ∂²/(4π)`. -/
theorem ccmIntertwines_jacobi : CCMIntertwines ccmMetaplecticJacobiFin ccmOscillatorJacobi := by
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single n c =>
    rw [ccmEvenHermiteSynthesis_single, map_smul, ccmMetaplecticJacobiFin_single, map_smul]
    congr 1
    rcases n with _ | m
    · rw [ccmOscillatorJacobi_hermiteUnit_zero]
      simp [ccmMetaplecticJacobiColumn, ccmMetaplecticLowerColumn, ccmEvenHermiteSynthesis_single,
        ccmMetaplecticCoeff]
    · rw [ccmOscillatorJacobi_hermiteUnit_succ]
      simp only [ccmMetaplecticJacobiColumn, ccmMetaplecticLowerColumn, map_add,
        ccmEvenHermiteSynthesis_single, ccmMetaplecticCoeff]
      rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by ring]

/-- `Φ` intertwines the number operator with `N = (i/2)(E - F) - 1/4`. -/
theorem ccmIntertwines_number : CCMIntertwines ccmNumberFin ccmOscillatorNumber := by
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single n c =>
    rw [ccmEvenHermiteSynthesis_single, map_smul, ccmOscillatorNumber_hermiteUnit,
      ccmNumberFin_single, ccmEvenHermiteSynthesis_single, smul_smul, mul_comm]

/-- `Φ` intertwines the CCM commutator `C = [J, N]` with the dilation generator `H`. -/
theorem ccmIntertwines_commutator :
    CCMIntertwines ⁅ccmMetaplecticJacobiFin, ccmNumberFin⁆ ccmOscillatorH := by
  rw [← ccmOscillator_lie_jacobi_number]
  exact ccmIntertwines_lie ccmIntertwines_jacobi ccmIntertwines_number

/-- **CCM Theorem 5.2(iv).**  The `sl₂`-triple built from the metaplectic Jacobi data is carried
by the even Hermite synthesis onto the even metaplectic (oscillator) triple, element by element. -/
theorem ccmMetaplectic_even_representation :
    IsSl2Triple ccmMetaplecticTripleH ccmMetaplecticTripleE ccmMetaplecticTripleF ∧
      IsSl2Triple (I • (ccmOscillatorE - ccmOscillatorF))
        ((2⁻¹ : ℂ) • (I • (ccmOscillatorE + ccmOscillatorF) - ccmOscillatorH))
        (-((2⁻¹ : ℂ) • (I • (ccmOscillatorE + ccmOscillatorF) + ccmOscillatorH))) ∧
      CCMIntertwines ccmMetaplecticTripleH (I • (ccmOscillatorE - ccmOscillatorF)) ∧
      CCMIntertwines ccmMetaplecticTripleE
        ((2⁻¹ : ℂ) • (I • (ccmOscillatorE + ccmOscillatorF) - ccmOscillatorH)) ∧
      CCMIntertwines ccmMetaplecticTripleF
        (-((2⁻¹ : ℂ) • (I • (ccmOscillatorE + ccmOscillatorF) + ccmOscillatorH))) := by
  refine ⟨ccmMetaplectic_isSl2Triple, ccmOscillatorCayley_isSl2Triple, ?_, ?_, ?_⟩
  · have h : I • (ccmOscillatorE - ccmOscillatorF) =
        (2 : ℂ) • ccmOscillatorNumber + (2⁻¹ : ℂ) • 1 := by
      rw [ccmOscillatorNumber_eq]
      module
    rw [h]
    exact ccmIntertwines_add (ccmIntertwines_smul _ ccmIntertwines_number)
      (ccmIntertwines_smul _ ccmIntertwines_one)
  · rw [← ccmOscillatorJacobi_eq]
    exact ccmIntertwines_smul _ (ccmIntertwines_sub ccmIntertwines_jacobi ccmIntertwines_commutator)
  · rw [← ccmOscillatorJacobi_eq]
    exact ccmIntertwines_neg
      (ccmIntertwines_smul _ (ccmIntertwines_add ccmIntertwines_jacobi ccmIntertwines_commutator))

/-! ## The unitary `ℓ²(ℕ) ≃ L²(ℝ)^ev` -/

theorem ccmSchwartz_toLp_smul (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    (c • f).toLp 2 volume = c • f.toLp 2 volume := by
  exact map_smul (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) c f

theorem ccmSchwartz_toLp_add (f g : 𝓢(ℝ, ℂ)) :
    (f + g).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume := by
  exact map_add (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) f g

theorem ccmSchwartz_toLp_zero : (0 : 𝓢(ℝ, ℂ)).toLp 2 volume = 0 := by
  exact map_zero (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))

theorem ccmHermiteUnit_toLp_mem_evenSubspace (n : ℕ) :
    (ccmHermiteUnit (2 * n)).toLp 2 volume ∈ evenSubspace := by
  rw [ccmHermiteUnit, ccmSchwartz_toLp_smul]
  exact evenSubspace.smul_mem _ (hermiteL2_mem_evenSubspace n)

/-- The normalized even Hermite functions in `L²(ℝ)^ev`. -/
def ccmEvenHermiteVector (n : ℕ) : evenSubspace :=
  ⟨(ccmHermiteUnit (2 * n)).toLp 2 volume, ccmHermiteUnit_toLp_mem_evenSubspace n⟩

theorem ccmEvenHermiteVector_eq_smul (n : ℕ) :
    ccmEvenHermiteVector n = ((ccmHermiteNorm (2 * n) : ℂ))⁻¹ • evenHermiteL2 n := by
  apply Subtype.ext
  change (ccmHermiteUnit (2 * n)).toLp 2 volume = _
  rw [ccmHermiteUnit, ccmSchwartz_toLp_smul]
  rfl

theorem orthonormal_ccmEvenHermiteVector : Orthonormal ℂ ccmEvenHermiteVector := by
  have h := orthonormal_hermiteSchwartz_toLp.comp (fun n : ℕ => 2 * n)
    (fun a b hab => by simpa using hab)
  constructor
  · intro n
    change ‖(ccmHermiteUnit (2 * n)).toLp 2 volume‖ = 1
    rw [ccmHermiteUnit, ccmSchwartz_toLp_smul]
    exact h.1 n
  · intro m n hmn
    change inner ℂ ((ccmHermiteUnit (2 * m)).toLp 2 volume)
      ((ccmHermiteUnit (2 * n)).toLp 2 volume) = 0
    rw [ccmHermiteUnit, ccmHermiteUnit, ccmSchwartz_toLp_smul, ccmSchwartz_toLp_smul]
    exact h.2 hmn

theorem ccmEvenHermiteVector_span_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range ccmEvenHermiteVector))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hu' : u ∈ evenHermiteL2Spanᗮ := by
    rw [evenHermiteL2Span, Submodule.mem_orthogonal']
    rw [Submodule.mem_orthogonal'] at hu
    intro v hv
    refine Submodule.span_induction (p := fun v _ => inner ℂ u v = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨n, rfl⟩
      have hn := hu (ccmEvenHermiteVector n) (Submodule.subset_span ⟨n, rfl⟩)
      have hN : ((ccmHermiteNorm (2 * n) : ℂ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ccmHermiteNorm_pos _).ne'
      rw [ccmEvenHermiteVector_eq_smul] at hn
      have hn' : inner ℂ (u : SoninL2)
          (((ccmHermiteNorm (2 * n) : ℂ))⁻¹ • (evenHermiteL2 n : SoninL2)) = 0 := hn
      rw [inner_smul_right] at hn'
      exact (mul_eq_zero.mp hn').resolve_left (inv_ne_zero hN)
    · exact inner_zero_right u
    · intro x y _ _ hx hy
      change inner ℂ (u : SoninL2) ((x : SoninL2) + (y : SoninL2)) = 0
      rw [inner_add_right]
      change inner ℂ u x + inner ℂ u y = 0
      rw [hx, hy, add_zero]
    · intro c x _ hx
      change inner ℂ (u : SoninL2) (c • (x : SoninL2)) = 0
      rw [inner_smul_right]
      change c * inner ℂ u x = 0
      rw [hx, mul_zero]
  rw [evenHermiteL2Span_orthogonal_eq_bot] at hu'
  exact hu'

/-- The even Hermite Hilbert basis of `L²(ℝ)^ev`. -/
def ccmEvenHermiteHilbertBasis : HilbertBasis ℕ ℂ evenSubspace :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_ccmEvenHermiteVector
    ccmEvenHermiteVector_span_orthogonal_eq_bot

@[simp] theorem ccmEvenHermiteHilbertBasis_apply (n : ℕ) :
    ccmEvenHermiteHilbertBasis n = ccmEvenHermiteVector n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot orthonormal_ccmEvenHermiteVector
    ccmEvenHermiteVector_span_orthogonal_eq_bot) n

/-- The unitary `ℓ²(ℕ) ≃ L²(ℝ)^ev`, `e_n ↦ ĥ_{2n}`, extending the even Hermite synthesis. -/
def ccmEvenHermiteUnitary : lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] evenSubspace :=
  ccmEvenHermiteHilbertBasis.repr.symm

theorem ccmEvenHermiteUnitary_single (n : ℕ) :
    ccmEvenHermiteUnitary (lp.single 2 n 1) = ccmEvenHermiteVector n := by
  rw [ccmEvenHermiteUnitary, HilbertBasis.repr_symm_single, ccmEvenHermiteHilbertBasis_apply]

/-- Finitely supported sequences inside `ℓ²(ℕ)`. -/
def ccmFinsuppToLp : (ℕ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  Finsupp.linearCombination ℂ fun n => lp.single 2 n (1 : ℂ)

/-- On finitely supported sequences the unitary is the even Hermite synthesis. -/
theorem ccmEvenHermiteUnitary_finsupp (x : ℕ →₀ ℂ) :
    ((ccmEvenHermiteUnitary (ccmFinsuppToLp x) : evenSubspace) : SoninL2) =
      (ccmEvenHermiteSynthesis x).toLp 2 volume := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, ccmSchwartz_toLp_zero]; rfl
  | add x y hx hy =>
    rw [map_add, map_add, Submodule.coe_add, hx, hy, map_add, ccmSchwartz_toLp_add]
  | single n c =>
    rw [ccmFinsuppToLp, Finsupp.linearCombination_single, map_smul, ccmEvenHermiteUnitary_single,
      ccmEvenHermiteSynthesis_single, Submodule.coe_smul, ccmSchwartz_toLp_smul]
    rfl

/-! ## The Gamma spectral moments -/

theorem semilocalArchimedeanJacobiCoefficient_eq_metaplectic (n : ℕ) :
    semilocalArchimedeanJacobiCoefficient n = (ccmMetaplecticJacobiCoefficient n : ℝ) := by
  have h1 := semilocalArchimedeanJacobiCoefficient_sq n
  have h2 := ccmMetaplecticJacobiCoefficient_sq n
  refine (pow_left_inj₀ (semilocalArchimedeanJacobiCoefficient_pos n).le
    (ccmMetaplecticJacobiCoefficient n).coe_nonneg two_ne_zero).mp ?_
  rw [h1, h2]
  push_cast
  ring

/-- Polynomial evaluation pairing `x ↦ Σ_n x_n p_n(s)` with the Gamma--Jacobi polynomials. -/
def ccmGammaJacobiPairing (s : ℝ) (x : ℕ →₀ ℂ) : ℂ :=
  x.sum fun n c => c * (((semilocalArchimedeanJacobiPolynomial n).eval s : ℝ) : ℂ)

theorem ccmGammaJacobiPairing_add (s : ℝ) (x y : ℕ →₀ ℂ) :
    ccmGammaJacobiPairing s (x + y) = ccmGammaJacobiPairing s x + ccmGammaJacobiPairing s y := by
  unfold ccmGammaJacobiPairing
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem ccmGammaJacobiPairing_single (s : ℝ) (n : ℕ) (c : ℂ) :
    ccmGammaJacobiPairing s (Finsupp.single n c) =
      c * (((semilocalArchimedeanJacobiPolynomial n).eval s : ℝ) : ℂ) := by
  unfold ccmGammaJacobiPairing
  rw [Finsupp.sum_single_index (zero_mul _)]

/-- The three-term recurrence: `J` is multiplication by `s` in the Gamma--Jacobi picture. -/
theorem ccmGammaJacobiPairing_jacobi (s : ℝ) (x : ℕ →₀ ℂ) :
    ccmGammaJacobiPairing s (ccmMetaplecticJacobiFin x) = s * ccmGammaJacobiPairing s x := by
  induction x using Finsupp.induction_linear with
  | zero => simp [ccmGammaJacobiPairing]
  | add x y hx hy => rw [map_add, ccmGammaJacobiPairing_add, ccmGammaJacobiPairing_add, hx, hy,
      mul_add]
  | single n c =>
    rw [ccmMetaplecticJacobiFin_single, ccmGammaJacobiPairing_single]
    have hrec : ∀ m : ℕ, (s : ℂ) * (((semilocalArchimedeanJacobiPolynomial (m + 1)).eval s : ℝ) : ℂ) =
        ccmMetaplecticCoeff m * (((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) +
          ccmMetaplecticCoeff (m + 1) *
            (((semilocalArchimedeanJacobiPolynomial (m + 2)).eval s : ℝ) : ℂ) := by
      intro m
      have h := semilocalArchimedeanJacobiPolynomial_eval_recurrence m s
      rw [semilocalArchimedeanJacobiCoefficient_eq_metaplectic,
        semilocalArchimedeanJacobiCoefficient_eq_metaplectic] at h
      unfold ccmMetaplecticCoeff
      exact_mod_cast h
    have hFinsupp : ∀ y : ℕ →₀ ℂ, ccmGammaJacobiPairing s (c • y) = c * ccmGammaJacobiPairing s y := by
      intro y
      unfold ccmGammaJacobiPairing
      rw [Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [hFinsupp]
    rcases n with _ | m
    · simp only [ccmMetaplecticJacobiColumn, ccmMetaplecticLowerColumn, zero_add,
        ccmGammaJacobiPairing_single]
      rw [semilocalArchimedeanJacobiPolynomial_eval_one,
        semilocalArchimedeanJacobiPolynomial_eval_zero,
        semilocalArchimedeanJacobiCoefficient_eq_metaplectic, ccmMetaplecticCoeff]
      have hpos : ((ccmMetaplecticJacobiCoefficient 0 : ℝ) : ℂ) ≠ 0 := by
        rw [← semilocalArchimedeanJacobiCoefficient_eq_metaplectic]
        exact Complex.ofReal_ne_zero.mpr (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
      push_cast
      field_simp
    · simp only [ccmMetaplecticJacobiColumn, ccmMetaplecticLowerColumn, ccmGammaJacobiPairing_add,
        ccmGammaJacobiPairing_single]
      rw [show m + 1 + 1 = m + 2 from rfl]
      linear_combination (-c) * hrec m

theorem ccmGammaJacobiPairing_jacobi_iterate (s : ℝ) (k : ℕ) :
    ccmGammaJacobiPairing s (ccmMetaplecticJacobiFin ^ k • Finsupp.single 0 1) = (s : ℂ) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, one_smul, ccmGammaJacobiPairing_single,
      semilocalArchimedeanJacobiPolynomial_eval_zero]
    simp
  | succ k ih =>
    rw [pow_succ', mul_smul, Module.End.smul_def, ccmGammaJacobiPairing_jacobi, ih, pow_succ']

theorem integral_ccmGammaJacobiPairing (x : ℕ →₀ ℂ) :
    ∫ s, ccmGammaJacobiPairing s x ∂semilocalArchimedeanGammaMeasure = x 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp [ccmGammaJacobiPairing]
  | add x y hx hy =>
    have hint : ∀ z : ℕ →₀ ℂ, Integrable (fun s => ccmGammaJacobiPairing s z)
        semilocalArchimedeanGammaMeasure := by
      intro z
      unfold ccmGammaJacobiPairing Finsupp.sum
      refine integrable_finsetSum _ fun n _ => ?_
      exact (integrable_coe_eval_semilocalArchimedeanGammaMeasure _).const_mul _
    simp_rw [ccmGammaJacobiPairing_add]
    rw [integral_add (hint x) (hint y), hx, hy, Finsupp.add_apply]
  | single n c =>
    simp_rw [ccmGammaJacobiPairing_single]
    rw [integral_const_mul, integral_complex_ofReal]
    have hgram := semilocalArchimedeanJacobiGram_eq_ite n 0
    simp only [semilocalArchimedeanJacobiGram, semilocalArchimedeanJacobiPolynomial_eval_zero,
      mul_one] at hgram
    rw [hgram, Finsupp.single_apply]
    split_ifs <;> simp_all

/-- **The spectral moments of the metaplectic Jacobi operator are the Gamma moments:**
`⟨e_0, J^k e_0⟩ = ∫ s^k dμ_Γ(s)`. -/
theorem ccmMetaplecticJacobi_moment_eq_gamma (k : ℕ) :
    (ccmMetaplecticJacobiFin ^ k • Finsupp.single 0 1) 0 = (ccmMetaplecticGammaMoment k : ℂ) := by
  rw [← integral_ccmGammaJacobiPairing]
  simp_rw [ccmGammaJacobiPairing_jacobi_iterate]
  rw [ccmMetaplecticGammaMoment]
  have h := integral_complex_ofReal (μ := semilocalArchimedeanGammaMeasure) (f := fun s : ℝ => s ^ k)
  push_cast at h
  exact h

/-- The Gamma measure is the unique probability measure with the Jacobi spectral moments. -/
theorem ccmMetaplecticJacobi_momentFiber_eq_singleton :
    {ν : ProbabilityMeasure ℝ | ∀ k : ℕ, Integrable (fun s : ℝ => s ^ k) (ν : Measure ℝ) ∧
        ((∫ s : ℝ, s ^ k ∂(ν : Measure ℝ) : ℝ) : ℂ) =
          (ccmMetaplecticJacobiFin ^ k • Finsupp.single 0 1) 0} =
      {ccmMetaplecticGammaProbabilityMeasure} := by
  rw [← ccmMetaplecticGammaMomentFiber_eq_singleton]
  ext ν
  simp only [Set.mem_setOf_eq, ccmMetaplecticGammaMomentFiber, ccmMetaplecticJacobi_moment_eq_gamma,
    Complex.ofReal_inj]

end RHTower
