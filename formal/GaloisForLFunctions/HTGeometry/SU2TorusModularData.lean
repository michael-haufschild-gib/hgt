import GaloisForLFunctions.RHTower.Sieve.RootsOfUnityFrequencies
import GaloisForLFunctions.RHTower.Sieve.ConcreteRoot
import Mathlib.Analysis.Fourier.ZMod

/-!
# Odd Fourier realization of `SU(2)` torus modular data

At `SU(2)` level `k`, put `r = k + 2`.  The modular `S`-kernel is the discrete sine transform on
labels `1, …, r - 1`.  Its unnormalised sine columns are the odd packets of characters of the
cyclic group of order `2r`.  This file proves their exact orthogonality, supplying the finite
Fourier ingredient needed to derive the torus `S²` (charge-conjugation) relation in Lean.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

open RHTower.Sieve

/-- The unnormalised odd Fourier packet underlying one column of the `SU(2)` torus sine kernel.
The label `a : Fin (r - 1)` represents the integrable weight `a + 1`. -/
noncomputable def su2TorusOddFourierPacket (r : ℕ) (a : Fin (r - 1)) :
    EuclideanSpace ℂ (Fin (2 * r)) :=
  expRow (2 * r) ((rootOfUnity (2 * r)) ^ ((a : ℕ) + 1)) -
    expRow (2 * r) ((rootOfUnity (2 * r)) ^ (2 * r - ((a : ℕ) + 1)))

/-- Exact discrete-sine orthogonality.  The odd Fourier packets for distinct `SU(2)` labels are
orthogonal; every packet has squared norm `4r`. -/
theorem inner_su2TorusOddFourierPacket {r : ℕ} (hr : 2 ≤ r)
    (a b : Fin (r - 1)) :
    ⟪su2TorusOddFourierPacket r a, su2TorusOddFourierPacket r b⟫_ℂ =
      if a = b then (4 * r : ℂ) else 0 := by
  let Q : ℕ := 2 * r
  let ζ : ℂ := rootOfUnity Q
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hζ : IsPrimitiveRoot ζ Q := by
    exact isPrimitiveRoot_rootOfUnity hQ.ne'
  have ha : (a : ℕ) + 1 < r := by omega
  have hb : (b : ℕ) + 1 < r := by omega
  have haQ : (a : ℕ) + 1 < Q := by dsimp [Q]; omega
  have hbQ : (b : ℕ) + 1 < Q := by dsimp [Q]; omega
  have hQaQ : Q - ((a : ℕ) + 1) < Q := by omega
  have hQbQ : Q - ((b : ℕ) + 1) < Q := by omega
  rw [su2TorusOddFourierPacket]
  change ⟪expRow Q (ζ ^ ((a : ℕ) + 1)) -
      expRow Q (ζ ^ (Q - ((a : ℕ) + 1))),
      expRow Q (ζ ^ ((b : ℕ) + 1)) -
        expRow Q (ζ ^ (Q - ((b : ℕ) + 1)))⟫_ℂ = _
  by_cases hab : a = b
  · subst b
    simp only [if_pos, inner_sub_left, inner_sub_right]
    have hcross₁ : ⟪expRow Q (ζ ^ ((a : ℕ) + 1)),
        expRow Q (ζ ^ (Q - ((a : ℕ) + 1)))⟫_ℂ = 0 :=
      inner_expRow_root_eq_zero hQ hζ haQ hQaQ (by omega)
    have hcross₂ : ⟪expRow Q (ζ ^ (Q - ((a : ℕ) + 1))),
        expRow Q (ζ ^ ((a : ℕ) + 1))⟫_ℂ = 0 :=
      inner_expRow_root_eq_zero hQ hζ hQaQ haQ (by omega)
    rw [inner_expRow_root_self hQ hζ, hcross₁, hcross₂,
      inner_expRow_root_self hQ hζ]
    dsimp [Q]
    push_cast
    ring
  · simp only [if_neg hab, inner_sub_left, inner_sub_right]
    have hab' : (a : ℕ) + 1 ≠ (b : ℕ) + 1 := by
      intro h
      apply hab
      apply Fin.ext
      omega
    have hcross₁ : ⟪expRow Q (ζ ^ ((a : ℕ) + 1)),
        expRow Q (ζ ^ ((b : ℕ) + 1))⟫_ℂ = 0 :=
      inner_expRow_root_eq_zero hQ hζ haQ hbQ hab'
    have hcross₂ : ⟪expRow Q (ζ ^ ((a : ℕ) + 1)),
        expRow Q (ζ ^ (Q - ((b : ℕ) + 1)))⟫_ℂ = 0 :=
      inner_expRow_root_eq_zero hQ hζ haQ hQbQ (by omega)
    have hcross₃ : ⟪expRow Q (ζ ^ (Q - ((a : ℕ) + 1))),
        expRow Q (ζ ^ ((b : ℕ) + 1))⟫_ℂ = 0 :=
      inner_expRow_root_eq_zero hQ hζ hQaQ hbQ (by omega)
    have hcross₄ : ⟪expRow Q (ζ ^ (Q - ((a : ℕ) + 1))),
        expRow Q (ζ ^ (Q - ((b : ℕ) + 1)))⟫_ℂ = 0 :=
      inner_expRow_root_eq_zero hQ hζ hQaQ hQbQ (by omega)
    rw [hcross₁, hcross₂, hcross₃, hcross₄]
    ring

/-- Every integrable `SU(2)` torus label contributes a nonzero odd Fourier packet. -/
theorem su2TorusOddFourierPacket_ne_zero {r : ℕ} (hr : 2 ≤ r)
    (a : Fin (r - 1)) : su2TorusOddFourierPacket r a ≠ 0 := by
  intro hzero
  have hinner := inner_su2TorusOddFourierPacket hr a a
  rw [if_pos rfl, hzero] at hinner
  have hnonzero : (4 * r : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : 4 * r ≠ 0)
  apply hnonzero
  simpa using hinner.symm

/-- The odd Fourier packets form an independent family of size `r - 1`, giving the expected
rank of the `SU(2)` torus state space at level `r - 2`. -/
theorem linearIndependent_su2TorusOddFourierPacket {r : ℕ} (hr : 2 ≤ r) :
    LinearIndependent ℂ (su2TorusOddFourierPacket r) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · exact su2TorusOddFourierPacket_ne_zero hr
  · intro a b hab
    rw [inner_su2TorusOddFourierPacket hr, if_neg hab]

/-- Synthesis of an `SU(2)` torus state from its odd Fourier sine packets. -/
noncomputable def su2TorusOddFourierSynthesis (r : ℕ) :
    (Fin (r - 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r)) :=
  Fintype.linearCombination ℂ (su2TorusOddFourierPacket r)

/-- The synthesis map preserves the Hermitian form up to its exact positive scale `4r`. -/
theorem inner_su2TorusOddFourierSynthesis {r : ℕ} (hr : 2 ≤ r)
    (x y : Fin (r - 1) → ℂ) :
    ⟪su2TorusOddFourierSynthesis r x, su2TorusOddFourierSynthesis r y⟫_ℂ =
      (4 * r : ℂ) * ∑ a, (starRingEnd ℂ) (x a) * y a := by
  rw [show su2TorusOddFourierSynthesis r =
      Fintype.linearCombination ℂ (su2TorusOddFourierPacket r) from rfl]
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_su2TorusOddFourierPacket hr]
  simp_rw [← Finset.mul_sum]
  simp_rw [show ∀ i j : Fin (r - 1),
      y j * (if i = j then (4 * r : ℂ) else 0) =
        if i = j then y j * (4 * r : ℂ) else 0 by
    intro i j
    split_ifs <;> simp]
  simp_rw [Fintype.sum_ite_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The Fourier synthesis map has no kernel: the `r - 1` integrable torus labels give genuine,
independent state directions. -/
theorem su2TorusOddFourierSynthesis_injective {r : ℕ} (hr : 2 ≤ r) :
    Function.Injective (su2TorusOddFourierSynthesis r) := by
  intro x y hxy
  have hzero : ∑ i, (x i - y i) • su2TorusOddFourierPacket r i = 0 := by
    change su2TorusOddFourierSynthesis r (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp
    (linearIndependent_su2TorusOddFourierPacket hr) (fun i => x i - y i) hzero
  funext i
  exact sub_eq_zero.mp (hcoeff i)

/-- Fourier analysis coordinates dual to the odd sine packets. -/
noncomputable def su2TorusOddFourierAnalysis (r : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * r))) : Fin (r - 1) → ℂ :=
  fun a => (4 * r : ℂ)⁻¹ * ⟪su2TorusOddFourierPacket r a, v⟫_ℂ

/-- Analysis recovers every coefficient of a synthesized torus state exactly. -/
theorem su2TorusOddFourierAnalysis_synthesis {r : ℕ} (hr : 2 ≤ r)
    (x : Fin (r - 1) → ℂ) :
    su2TorusOddFourierAnalysis r (su2TorusOddFourierSynthesis r x) = x := by
  funext a
  unfold su2TorusOddFourierAnalysis
  rw [show su2TorusOddFourierSynthesis r =
      Fintype.linearCombination ℂ (su2TorusOddFourierPacket r) from rfl]
  rw [Fintype.linearCombination_apply, inner_sum]
  simp_rw [inner_smul_right, inner_su2TorusOddFourierPacket hr]
  simp_rw [show ∀ j : Fin (r - 1),
      x j * (if a = j then (4 * r : ℂ) else 0) =
        if a = j then x j * (4 * r : ℂ) else 0 by
    intro j
    split_ifs <;> simp]
  rw [Fintype.sum_ite_eq]
  have hnonzero : (4 * r : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : 4 * r ≠ 0)
  calc
    (4 * r : ℂ)⁻¹ * (x a * (4 * r : ℂ)) =
        ((4 * r : ℂ)⁻¹ * (4 * r : ℂ)) * x a := by ring
    _ = x a := by rw [inv_mul_cancel₀ hnonzero, one_mul]

/-- Linear extension of odd Fourier analysis to the ambient cyclic Fourier space. -/
noncomputable def su2TorusOddFourierAnalysisLinear (r : ℕ) :
    EuclideanSpace ℂ (Fin (2 * r)) →ₗ[ℂ] (Fin (r - 1) → ℂ) :=
  { toFun := su2TorusOddFourierAnalysis r
    map_add' := by
      intro x y
      funext a
      simp [su2TorusOddFourierAnalysis, inner_add_right, mul_add]
    map_smul' := by
      intro c x
      funext a
      change (4 * r : ℂ)⁻¹ *
        ⟪su2TorusOddFourierPacket r a, c • x⟫_ℂ =
        c • ((4 * r : ℂ)⁻¹ * ⟪su2TorusOddFourierPacket r a, x⟫_ℂ)
      rw [inner_smul_right]
      simp only [smul_eq_mul]
      ring }

@[simp]
theorem su2TorusOddFourierAnalysisLinear_apply (r : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * r))) :
    su2TorusOddFourierAnalysisLinear r v = su2TorusOddFourierAnalysis r v := rfl

/-- Orthogonal projector from the full cyclic Fourier space to the exact `SU(2)` odd packet
state space.  This is a finite-dimensional state-space construction, not yet a construction of
the Reshetikhin--Turaev TQFT. -/
noncomputable def su2TorusOddFourierProjector (r : ℕ) :
    EuclideanSpace ℂ (Fin (2 * r)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r)) :=
  (su2TorusOddFourierSynthesis r).comp (su2TorusOddFourierAnalysisLinear r)

/-- The projector fixes every synthesized `SU(2)` torus state. -/
theorem su2TorusOddFourierProjector_apply_synthesis {r : ℕ} (hr : 2 ≤ r)
    (x : Fin (r - 1) → ℂ) :
    su2TorusOddFourierProjector r (su2TorusOddFourierSynthesis r x) =
      su2TorusOddFourierSynthesis r x := by
  simp only [su2TorusOddFourierProjector, LinearMap.comp_apply,
    su2TorusOddFourierAnalysisLinear_apply]
  rw [su2TorusOddFourierAnalysis_synthesis hr]

/-- The odd Fourier projector is idempotent. -/
theorem su2TorusOddFourierProjector_idempotent {r : ℕ} (hr : 2 ≤ r)
    (v : EuclideanSpace ℂ (Fin (2 * r))) :
    su2TorusOddFourierProjector r (su2TorusOddFourierProjector r v) =
      su2TorusOddFourierProjector r v := by
  simp only [su2TorusOddFourierProjector, LinearMap.comp_apply,
    su2TorusOddFourierAnalysisLinear_apply]
  rw [su2TorusOddFourierAnalysis_synthesis hr]

/-- The odd Fourier projector is self-adjoint for the ambient Hermitian form. -/
theorem inner_su2TorusOddFourierProjector_left (r : ℕ)
    (v w : EuclideanSpace ℂ (Fin (2 * r))) :
    ⟪su2TorusOddFourierProjector r v, w⟫_ℂ =
      ⟪v, su2TorusOddFourierProjector r w⟫_ℂ := by
  have hscale : (starRingEnd ℂ) ((4 * r : ℂ)⁻¹) = (4 * r : ℂ)⁻¹ := by
    have hreal : (4 * r : ℂ) = ((4 * r : ℝ) : ℂ) := by norm_num
    rw [hreal, map_inv₀, Complex.conj_ofReal]
  simp only [su2TorusOddFourierProjector, LinearMap.comp_apply,
    su2TorusOddFourierAnalysisLinear_apply]
  rw [show su2TorusOddFourierSynthesis r =
      Fintype.linearCombination ℂ (su2TorusOddFourierPacket r) from rfl]
  simp only [Fintype.linearCombination_apply, sum_inner, inner_sum]
  simp_rw [inner_smul_left, inner_smul_right, su2TorusOddFourierAnalysis]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_mul, hscale, inner_conj_symm]
  ring

/-- The Weyl-odd carrier for the `SU(2)` torus at shifted level `r`: functions on the cyclic
group of order `2r` that are anti-invariant under inversion.  At a genuine level (`2 ≤ r`), the
fixed points vanish automatically, leaving the expected `r - 1` state directions. -/
noncomputable def su2TorusWeylOddSubmodule (r : ℕ) :
    Submodule ℂ (ZMod (2 * r) → ℂ) where
  carrier := {f | f.Odd}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro f g hf hg x
    change f (-x) + g (-x) = -(f x + g x)
    rw [hf x, hg x]
    ring
  smul_mem' := by
    intro c f hf x
    change c • f (-x) = -(c • f x)
    rw [hf x]
    simp

/-- Positive representatives for the nontrivial Weyl orbits in `ZMod (2r)`. -/
def su2TorusWeylPositiveResidue (r : ℕ) (a : Fin (r - 1)) : ZMod (2 * r) :=
  (((a : ℕ) + 1 : ℕ) : ZMod (2 * r))

/-- Signed delta function on one nontrivial Weyl orbit. -/
noncomputable def su2TorusWeylOddBasisVector (r : ℕ) (a : Fin (r - 1)) :
    ZMod (2 * r) → ℂ :=
  fun x => if x = su2TorusWeylPositiveResidue r a then 1 else
    if x = -su2TorusWeylPositiveResidue r a then -1 else 0

theorem su2TorusWeylOddBasisVector_odd {r : ℕ} (hr : 2 ≤ r) (a : Fin (r - 1)) :
    (su2TorusWeylOddBasisVector r a).Odd := by
  let p : ZMod (2 * r) := su2TorusWeylPositiveResidue r a
  have hpval : p.val = (a : ℕ) + 1 := by
    dsimp [p, su2TorusWeylPositiveResidue]
    apply ZMod.val_natCast_of_lt
    omega
  have hpne : -p ≠ p := by
    intro h
    rcases (ZMod.neg_eq_self_iff p).mp h with hpzero | htwo
    · have hval := congrArg ZMod.val hpzero
      rw [hpval, ZMod.val_zero] at hval
      omega
    · rw [hpval] at htwo
      omega
  intro x
  change (if -x = p then 1 else if -x = -p then -1 else 0) =
    -(if x = p then 1 else if x = -p then -1 else 0)
  by_cases hxpos : x = p
  · subst x
    simp [hpne]
  by_cases hxneg : x = -p
  · subst x
    simp [hpne]
  have hnxpos : -x ≠ p := by
    intro h
    apply hxneg
    simpa only [neg_neg] using congrArg Neg.neg h
  have hnxneg : -x ≠ -p := by
    intro h
    apply hxpos
    simpa only [neg_neg] using congrArg Neg.neg h
  simp [hxpos, hxneg, hnxpos, hnxneg]

theorem su2TorusWeylPositiveResidue_ne_neg {r : ℕ} (hr : 2 ≤ r)
    (a b : Fin (r - 1)) :
    su2TorusWeylPositiveResidue r a ≠ -su2TorusWeylPositiveResidue r b := by
  intro h
  change (((a : ℕ) + 1 : ℕ) : ZMod (2 * r)) =
    -(((b : ℕ) + 1 : ℕ) : ZMod (2 * r)) at h
  have hsum : ((((a : ℕ) + 1) + ((b : ℕ) + 1) : ℕ) : ZMod (2 * r)) = 0 := by
    rw [Nat.cast_add]
    rw [h]
    simp
  have hdvd : 2 * r ∣ ((a : ℕ) + 1) + ((b : ℕ) + 1) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hsum
  have hpos : 0 < ((a : ℕ) + 1) + ((b : ℕ) + 1) := by omega
  have hlt : ((a : ℕ) + 1) + ((b : ℕ) + 1) < 2 * r := by omega
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd

/-- The orbit-delta vectors, now regarded as `SU(2)` Weyl-odd states. -/
noncomputable def su2TorusWeylOddBasis (r : ℕ) (hr : 2 ≤ r) (a : Fin (r - 1)) :
    su2TorusWeylOddSubmodule r :=
  ⟨su2TorusWeylOddBasisVector r a, su2TorusWeylOddBasisVector_odd hr a⟩

theorem su2TorusWeylOddBasis_apply_positive {r : ℕ} (hr : 2 ≤ r)
    (a b : Fin (r - 1)) :
    (su2TorusWeylOddBasis r hr b : ZMod (2 * r) → ℂ)
        (su2TorusWeylPositiveResidue r a) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp only [if_pos]
    unfold su2TorusWeylOddBasis su2TorusWeylOddBasisVector
    simp
  · simp only [if_neg hab]
    have hposne : su2TorusWeylPositiveResidue r a ≠ su2TorusWeylPositiveResidue r b := by
      intro h
      apply hab
      apply Fin.ext
      have hval := congrArg ZMod.val h
      simp only [su2TorusWeylPositiveResidue] at hval
      rw [ZMod.val_natCast_of_lt (by omega),
        ZMod.val_natCast_of_lt (by omega)] at hval
      omega
    change su2TorusWeylOddBasisVector r b (su2TorusWeylPositiveResidue r a) = 0
    unfold su2TorusWeylOddBasisVector
    simp only [hposne, su2TorusWeylPositiveResidue_ne_neg hr a b, if_false]

theorem linearIndependent_su2TorusWeylOddBasis {r : ℕ} (hr : 2 ≤ r) :
    LinearIndependent ℂ (su2TorusWeylOddBasis r hr) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have hfun := congrArg (su2TorusWeylOddSubmodule r).subtype hg
  simp only [map_sum, map_smul, map_zero] at hfun
  change ∑ x, g x • (su2TorusWeylOddBasis r hr x : ZMod (2 * r) → ℂ) = 0 at hfun
  have heval := congrFun hfun (su2TorusWeylPositiveResidue r a)
  simp_rw [Finset.sum_apply, Pi.smul_apply,
    su2TorusWeylOddBasis_apply_positive hr a] at heval
  simpa using heval

/-- The Weyl-odd carrier has at least the expected `r - 1` independent torus directions. -/
theorem su2TorusWeylOdd_finrank_lower_bound {r : ℕ} (hr : 2 ≤ r) :
    r - 1 ≤ Module.finrank ℂ (su2TorusWeylOddSubmodule r) := by
  have hne : 2 * r ≠ 0 := by omega
  letI : NeZero (2 * r) := ⟨hne⟩
  letI : Fintype (ZMod (2 * r)) := ZMod.fintype (2 * r)
  letI : FiniteDimensional ℂ (ZMod (2 * r) → ℂ) :=
    FiniteDimensional.finiteDimensional_pi ℂ
  simpa using (linearIndependent_su2TorusWeylOddBasis hr).fintype_card_le_finrank

/-- Positive orbit coordinates determine every Weyl-odd state.  The two fixed residues vanish,
and every other residue is exactly one positive representative or its negative. -/
theorem su2TorusWeylOdd_value_eq_zero_of_positive_coordinates {r : ℕ} (hr : 2 ≤ r)
    (f : su2TorusWeylOddSubmodule r)
    (h : ∀ a : Fin (r - 1), f.1 (su2TorusWeylPositiveResidue r a) = 0)
    (x : ZMod (2 * r)) : f.1 x = 0 := by
  have hn : 2 * r ≠ 0 := by omega
  letI : NeZero (2 * r) := ⟨hn⟩
  have hxlt : x.val < 2 * r := x.val_lt
  by_cases hzero : x.val = 0
  · have hx : x = 0 := (ZMod.val_eq_zero x).mp hzero
    subst x
    exact f.2.map_zero
  by_cases hmid : x.val = r
  · have hself : -x = x := (ZMod.neg_eq_self_iff x).mpr (Or.inr (by omega))
    have hneg : f.1 x = -f.1 x := by simpa [hself] using f.2 x
    have htwo : (2 : ℂ) * f.1 x = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  by_cases hlt : x.val < r
  · let a : Fin (r - 1) := ⟨x.val - 1, by omega⟩
    have hp : su2TorusWeylPositiveResidue r a = x := by
      apply ZMod.val_injective (2 * r)
      dsimp [su2TorusWeylPositiveResidue, a]
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    simpa [hp] using h a
  · have hgt : r < x.val := by omega
    let a : Fin (r - 1) := ⟨2 * r - x.val - 1, by omega⟩
    have hp : su2TorusWeylPositiveResidue r a = -x := by
      apply eq_neg_of_add_eq_zero_left
      rw [← ZMod.natCast_zmod_val x]
      change ((↑((a : ℕ) + 1) : ZMod (2 * r)) + ↑x.val) = 0
      rw [← Nat.cast_add]
      dsimp [a]
      have hsum : 2 * r - x.val - 1 + 1 + x.val = 2 * r := by omega
      rw [hsum, ZMod.natCast_self]
    have hx : x = -su2TorusWeylPositiveResidue r a := by
      simpa using (congrArg Neg.neg hp).symm
    rw [hx, f.2, h a]
    simp

/-- Evaluation on one representative of each nontrivial Weyl orbit. -/
noncomputable def su2TorusWeylOddPositiveCoordinates (r : ℕ) :
    su2TorusWeylOddSubmodule r →ₗ[ℂ] (Fin (r - 1) → ℂ) where
  toFun f a := f.1 (su2TorusWeylPositiveResidue r a)
  map_add' := by
    intro f g
    ext a
    rfl
  map_smul' := by
    intro c f
    ext a
    rfl

theorem su2TorusWeylOddPositiveCoordinates_injective {r : ℕ} (hr : 2 ≤ r) :
    Function.Injective (su2TorusWeylOddPositiveCoordinates r) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have hcoordinates : ∀ a : Fin (r - 1),
      (f - g).1 (su2TorusWeylPositiveResidue r a) = 0 := by
    intro a
    have ha := congrFun hfg a
    change f.1 (su2TorusWeylPositiveResidue r a) =
      g.1 (su2TorusWeylPositiveResidue r a) at ha
    change f.1 (su2TorusWeylPositiveResidue r a) -
      g.1 (su2TorusWeylPositiveResidue r a) = 0
    exact sub_eq_zero.mpr ha
  have hzero := su2TorusWeylOdd_value_eq_zero_of_positive_coordinates hr (f - g)
    hcoordinates x
  change f.1 x - g.1 x = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- Exact dimension of the `SU(2)` Weyl-odd torus carrier. -/
theorem su2TorusWeylOdd_finrank {r : ℕ} (hr : 2 ≤ r) :
    Module.finrank ℂ (su2TorusWeylOddSubmodule r) = r - 1 := by
  have hne : 2 * r ≠ 0 := by omega
  letI : NeZero (2 * r) := ⟨hne⟩
  letI : Fintype (ZMod (2 * r)) := ZMod.fintype (2 * r)
  letI : FiniteDimensional ℂ (ZMod (2 * r) → ℂ) :=
    FiniteDimensional.finiteDimensional_pi ℂ
  apply Nat.le_antisymm
  · have hle := LinearMap.finrank_le_finrank_of_injective
      (su2TorusWeylOddPositiveCoordinates_injective hr)
    simpa using hle
  · exact su2TorusWeylOdd_finrank_lower_bound hr

/-- Explicit coordinate equivalence between the Weyl-odd torus state space and its `r - 1`
positive Weyl-orbit coordinates. -/
noncomputable def su2TorusWeylOddPositiveCoordinatesEquiv (r : ℕ) (hr : 2 ≤ r) :
    su2TorusWeylOddSubmodule r ≃ₗ[ℂ] (Fin (r - 1) → ℂ) := by
  have hne : 2 * r ≠ 0 := by omega
  letI : NeZero (2 * r) := ⟨hne⟩
  letI : Fintype (ZMod (2 * r)) := ZMod.fintype (2 * r)
  letI : FiniteDimensional ℂ (ZMod (2 * r) → ℂ) :=
    FiniteDimensional.finiteDimensional_pi ℂ
  apply LinearMap.linearEquivOfInjective (su2TorusWeylOddPositiveCoordinates r)
    (su2TorusWeylOddPositiveCoordinates_injective hr)
  rw [su2TorusWeylOdd_finrank hr, Module.finrank_fintype_fun_eq_card]
  simp

theorem su2TorusWeylOddPositiveCoordinatesEquiv_apply {r : ℕ} (hr : 2 ≤ r)
    (f : su2TorusWeylOddSubmodule r) (a : Fin (r - 1)) :
    su2TorusWeylOddPositiveCoordinatesEquiv r hr f a =
      f.1 (su2TorusWeylPositiveResidue r a) := by
  change su2TorusWeylOddPositiveCoordinates r f a = _
  rfl

/-- The unnormalised finite Fourier operator preserves the `SU(2)` Weyl-odd torus carrier. -/
noncomputable def su2TorusWeylOddFourier (r : ℕ) [NeZero (2 * r)] :
    su2TorusWeylOddSubmodule r →ₗ[ℂ] su2TorusWeylOddSubmodule r where
  toFun f := ⟨ZMod.dft f.1, ZMod.dft_odd_iff.mpr f.2⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (ZMod.dft (N := 2 * r)).map_add f.1 g.1
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact (ZMod.dft (N := 2 * r)).map_smul c f.1

/-- On the Weyl-odd carrier, Fourier square is the negative scalar `−2r`: ordinary Fourier
reflection becomes `−id`. -/
theorem su2TorusWeylOddFourier_sq {r : ℕ} [NeZero (2 * r)]
    (f : su2TorusWeylOddSubmodule r) :
    su2TorusWeylOddFourier r (su2TorusWeylOddFourier r f) =
      -((2 * r : ℂ)) • f := by
  apply Subtype.ext
  change ZMod.dft (ZMod.dft f.1) = _
  rw [ZMod.dft_dft]
  funext j
  rw [f.2]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The standard phase and square-root normalization for the `SU(2)` torus `S`-operator. -/
noncomputable def su2TorusWeylOddFourierScale (r : ℕ) : ℂ :=
  Complex.I * (((Real.sqrt (2 * r : ℝ)) : ℂ)⁻¹)

theorem su2TorusWeylOddFourierScale_sq_mul_neg {r : ℕ} (hr : 0 < r) :
    su2TorusWeylOddFourierScale r * su2TorusWeylOddFourierScale r *
      (-((2 * r : ℂ))) = 1 := by
  have hpos : 0 < (2 * r : ℝ) := by positivity
  have hsqrtne : ((Real.sqrt (2 * r : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  have hsquare : ((Real.sqrt (2 * r : ℝ) : ℝ) : ℂ) ^ 2 = (2 * r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le]
    norm_num
  unfold su2TorusWeylOddFourierScale
  field_simp
  rw [Complex.I_sq, hsquare]
  ring

/-- Normalized finite Fourier transform on the Weyl-odd carrier.  This is the exact torus
`SU(2)` modular `S`-operator at shifted level `r`, before adding the remaining RT surgery and
mapping-class representation layers. -/
noncomputable def su2TorusWeylS (r : ℕ) [NeZero (2 * r)] :
    su2TorusWeylOddSubmodule r →ₗ[ℂ] su2TorusWeylOddSubmodule r :=
  su2TorusWeylOddFourierScale r • su2TorusWeylOddFourier r

/-- Closed `SU(2)` torus modular relation: on the Weyl-odd state carrier `S²` is charge
conjugation, which is the identity because every `SU(2)` integrable label is self-dual. -/
theorem su2TorusWeylS_sq {r : ℕ} [NeZero (2 * r)] (hr : 2 ≤ r)
    (f : su2TorusWeylOddSubmodule r) :
    su2TorusWeylS r (su2TorusWeylS r f) = f := by
  simp only [su2TorusWeylS, LinearMap.smul_apply]
  rw [map_smul, su2TorusWeylOddFourier_sq]
  rw [← mul_smul, ← mul_smul, su2TorusWeylOddFourierScale_sq_mul_neg (by omega), one_smul]

/-- The calibrated genus-one trace: the square of the normalized Weyl-odd `S`-operator has
trace `r - 1`.  This is the finite torus-side identity required before any RT surgery or
mapping-torus trace identification can be stated. -/
theorem su2TorusWeylS_square_trace {r : ℕ} [NeZero (2 * r)] (hr : 2 ≤ r) :
    LinearMap.trace ℂ (su2TorusWeylOddSubmodule r)
      (su2TorusWeylS r * su2TorusWeylS r) = (r - 1 : ℂ) := by
  letI : Fintype (ZMod (2 * r)) := ZMod.fintype (2 * r)
  letI : FiniteDimensional ℂ (ZMod (2 * r) → ℂ) :=
    FiniteDimensional.finiteDimensional_pi ℂ
  have hsq : su2TorusWeylS r * su2TorusWeylS r = 1 := by
    apply LinearMap.ext
    intro f
    change su2TorusWeylS r (su2TorusWeylS r f) = f
    exact su2TorusWeylS_sq hr f
  rw [hsq, LinearMap.trace_one, su2TorusWeylOdd_finrank hr]
  rw [Nat.cast_sub (by omega)]
  norm_num

end GaloisForLFunctions.HTGeometry
