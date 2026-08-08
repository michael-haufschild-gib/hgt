import GaloisForLFunctions.HTGeometry.ScalarEigenDifferentialTorsor
import GaloisForLFunctions.HTGeometry.MutualGeneratorMobius
import Mathlib.GroupTheory.OrderOfElement

namespace GaloisForLFunctions.HTGeometry

open scoped Differential Polynomial
open GaloisForLFunctions

noncomputable section

variable {C T : Type*} [Field C] [Field T] [Algebra C T] [Differential T]

/-- A derivation-compatible coefficient-fixing automorphism that fixes a differential generator
is the identity. -/
theorem algEquiv_eq_refl_of_differential_generator_fixed
    (tau : T ≃ₐ[C] T) (htau : ∀ z : T, tau z′ = (tau z)′)
    (q : T) (hqgen : differentialAdjoin C ({q} : Set T) = ⊤)
    (hq : tau q = q) : tau = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro z
  have hz : z ∈ differentialAdjoin C ({q} : Set T) := by
    rw [hqgen]
    trivial
  rw [differentialAdjoin] at hz
  apply IntermediateField.adjoin_induction C
    (s := differentialJetSet ({q} : Set T))
    (p := fun w _ => tau w = (AlgEquiv.refl : T ≃ₐ[C] T) w)
  · rintro w ⟨v, hv, n, rfl⟩
    have hvq : v = q := Set.mem_singleton_iff.mp hv
    subst v
    have hjet : ∀ m : ℕ, tau (differentialJet m q) = differentialJet m (tau q) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [differentialJet_succ, htau, ih, differentialJet_succ]
    rw [hjet, hq]
    rfl
  · intro c
    simp
  · intro a b _ _ ha hb
    simpa [map_add] using congrArg₂ (· + ·) ha hb
  · intro a _ ha
    simpa [map_inv₀] using congrArg Inv.inv ha
  · intro a b _ _ ha hb
    simpa [map_mul] using congrArg₂ (· * ·) ha hb
  · exact hz

/-- The order of a differential automorphism acting by a constant-unit eigenvalue on a differential
generator is exactly the multiplicative order of that unit. -/
theorem DifferentialAlgEquiv.orderOf_eq_orderOf_unit_of_generator
    (sigma : DifferentialAlgEquiv C T)
    (q : T) (hq0 : q ≠ 0)
    (hqgen : differentialAdjoin C ({q} : Set T) = ⊤)
    (lam : Cˣ)
    (haction : sigma.toAlgEquiv q = q * algebraMap C T (lam : C)) :
    orderOf sigma.toAlgEquiv = orderOf lam := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  have hpowActionAll : ∀ m : ℕ, (sigma.toAlgEquiv ^ m) q =
      q * algebraMap C T ((lam ^ m : Cˣ) : C) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply, haction, map_mul,
          (sigma.toAlgEquiv ^ m).commutes, ih]
        simp [pow_succ]
        ring
  have hpowAction := hpowActionAll n
  have hpowDerivAll : ∀ m : ℕ, ∀ z : T,
      (sigma.toAlgEquiv ^ m) z′ = ((sigma.toAlgEquiv ^ m) z)′ := by
    intro m
    induction m with
    | zero =>
        intro z
        rfl
    | succ m ih =>
        intro z
        rw [pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigma.map_deriv']
        exact ih (sigma.toAlgEquiv z)
  have hpowDeriv := hpowDerivAll n
  constructor
  · intro hsigma
    have hqeq := congrArg (fun e : T ≃ₐ[C] T => e q) hsigma
    rw [hpowAction] at hqeq
    have hcoeff : algebraMap C T (((lam ^ n : Cˣ) : C)) = 1 := by
      apply mul_left_cancel₀ hq0
      simpa using hqeq
    apply Units.ext
    apply (algebraMap C T).injective
    simpa using hcoeff
  · intro hlam
    apply algEquiv_eq_refl_of_differential_generator_fixed
      (sigma.toAlgEquiv ^ n) hpowDeriv q hqgen
    rw [hpowAction, hlam]
    simp

/-- A differential automorphism translating a differential generator by one has infinite order in
characteristic zero. -/
theorem DifferentialAlgEquiv.orderOf_eq_zero_of_translate_one_generator
    [CharZero C]
    (sigma : DifferentialAlgEquiv C T)
    (q : T)
    (haction : sigma.toAlgEquiv q = q + algebraMap C T 1) :
    orderOf sigma.toAlgEquiv = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hsigma
  have hpowActionAll : ∀ m : ℕ, (sigma.toAlgEquiv ^ m) q =
      q + algebraMap C T (m : C) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply, haction, map_add,
          (sigma.toAlgEquiv ^ m).commutes, ih]
        push_cast
        ring
  have hqeq := congrArg (fun e : T ≃ₐ[C] T => e q) hsigma
  rw [hpowActionAll n] at hqeq
  have hnzeroT : algebraMap C T (n : C) = 0 := by
    apply add_left_cancel (a := q)
    simpa using hqeq
  have hnzeroC : (n : C) = 0 :=
    (algebraMap C T).injective (by simpa using hnzeroT)
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hnzeroC

section ProjectiveDisjointness

variable [Differential C] [DifferentialAlgebra C T] [CharZero T]

/-- Multiplicative and additive projective normal forms cannot coexist, even on different
hypertranscendental differential generators. -/
theorem DifferentialAlgEquiv.not_unit_eigenvector_and_translate_one_on_generators
    (sigma : DifferentialAlgEquiv C T)
    (q r : T) (hq : HypertranscendentalOver C q)
    (hr : HypertranscendentalOver C r)
    (hqgen : differentialAdjoin C ({q} : Set T) = ⊤)
    (hrgen : differentialAdjoin C ({r} : Set T) = ⊤)
    (lam : Cˣ)
    (hqaction : sigma.toAlgEquiv q = q * algebraMap C T (lam : C))
    (hraction : sigma.toAlgEquiv r = r + algebraMap C T 1) : False := by
  have hqr : q ∈ differentialAdjoin C ({r} : Set T) := by
    rw [hrgen]
    trivial
  have hrq : r ∈ differentialAdjoin C ({q} : Set T) := by
    rw [hqgen]
    trivial
  obtain ⟨A, B, c, d, hdet, hmob⟩ := mutual_generator_mobius hq hr hrq hqr
  let AT : T := algebraMap C T A
  let BT : T := algebraMap C T B
  let cT : T := algebraMap C T c
  let dT : T := algebraMap C T d
  let lamT : T := algebraMap C T (lam : C)
  have hmobT : r * (cT * q + dT) = AT * q + BT := by
    simpa [AT, BT, cT, dT] using hmob
  have hmobSigma :
      (r + 1) * (cT * (q * lamT) + dT) = AT * (q * lamT) + BT := by
    have hs := congrArg sigma.toAlgEquiv hmobT
    simpa [AT, BT, cT, dT, lamT, hqaction, hraction, map_add, map_mul,
      sigma.toAlgEquiv.commutes] using hs
  let D0 : T := cT * q + dT
  let D1 : T := cT * (q * lamT) + dT
  let N0 : T := AT * q + BT
  let N1 : T := AT * (q * lamT) + BT
  have hmob0 : r * D0 = N0 := by simpa [D0, N0] using hmobT
  have hmob1 : (r + 1) * D1 = N1 := by simpa [D1, N1] using hmobSigma
  have hshift0 : (r + 1) * D0 = N0 + D0 := by
    calc
      (r + 1) * D0 = r * D0 + D0 := by ring
      _ = N0 + D0 := by rw [hmob0]
  have hclear : (N0 + D0) * D1 - N1 * D0 = 0 := by
    calc
      (N0 + D0) * D1 - N1 * D0 = ((r + 1) * D0) * D1 - N1 * D0 := by
        rw [hshift0]
      _ = ((r + 1) * D1) * D0 - N1 * D0 := by ring
      _ = N1 * D0 - N1 * D0 := by rw [hmob1]
      _ = 0 := sub_self _
  let P : C[X] :=
    Polynomial.monomial 2 (c * c * (lam : C)) +
      Polynomial.monomial 1 ((1 - (lam : C)) * (A * d - B * c) +
        c * d * (1 + (lam : C))) +
      Polynomial.C (d * d)
  have hPeval : Polynomial.aeval q P = 0 := by
    have hexpand : Polynomial.aeval q P = (N0 + D0) * D1 - N1 * D0 := by
      simp [P, N0, N1, D0, D1, AT, BT, cT, dT, lamT]
      ring
    rw [hexpand]
    exact hclear
  have hqtrans : Transcendental C q := by
    simpa using hypertranscendentalOver_jet_transcendental hq 0
  have hPzero : P = 0 := by
    by_contra hP
    exact hqtrans ⟨P, hP, hPeval⟩
  have hd2 : d * d = 0 := by
    have hcoeff := congrArg (fun Q : C[X] => Q.coeff 0) hPzero
    simpa [P, Polynomial.coeff_monomial] using hcoeff
  have hd : d = 0 := (mul_self_eq_zero.mp hd2)
  have hc : c = 0 := by
    have hcoeff := congrArg (fun Q : C[X] => Q.coeff 2) hPzero
    simpa [P, hd, Polynomial.coeff_monomial] using hcoeff
  apply hdet
  simp [hc, hd]

end ProjectiveDisjointness

end

end GaloisForLFunctions.HTGeometry
