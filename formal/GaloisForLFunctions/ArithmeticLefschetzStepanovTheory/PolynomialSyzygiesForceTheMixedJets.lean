import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheEulerJetsOfStepanovsAuxiliary
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.ExactVanishingCostsTheDegree

/-!
# Polynomial syzygies force mixed Stepanov jets

Differentiating a polynomial syzygy transfers an Euler derivative between its
two factors. Iterating this identity forces all mixed jets of the Adams
auxiliary at fixed points. At a point with nonzero coordinates, these imply
ordinary vanishing of the same order, so exactness still pays the degree bound.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ : Type*}

theorem integralEuler_mul (j : σ) (F G : MvPolynomial σ ℤ) :
    integralEuler j (F * G) = integralEuler j F * G + F * integralEuler j G := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Coordinate Euler derivatives, with the head of the word acting last. -/
def integralEulerWord (L : List σ) : Module.End ℤ (MvPolynomial σ ℤ) :=
  L.foldr (fun j E => (integralEuler j).toLinearMap * E) 1

theorem integralEulerWord_nil (F : MvPolynomial σ ℤ) : integralEulerWord [] F = F := rfl

theorem integralEulerWord_cons (j : σ) (L : List σ) (F : MvPolynomial σ ℤ) :
    integralEulerWord (j :: L) F = integralEuler j (integralEulerWord L F) := rfl

theorem integralEulerWord_append (L K : List σ) (F : MvPolynomial σ ℤ) :
    integralEulerWord (L ++ K) F = integralEulerWord L (integralEulerWord K F) := by
  induction L with
  | nil => rfl
  | cons j L ih => exact congrArg (integralEuler j) ih

/-- A polynomial moment differentiating only the first factors along a mixed word. -/
def stepanovWordMoment {m : ℕ} (L : List σ) (f g : Fin m → MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ := ∑ i, integralEulerWord L (f i) * g i

theorem integralEuler_stepanovWordMoment {m : ℕ} (j : σ) (L : List σ)
    (f g : Fin m → MvPolynomial σ ℤ) :
    integralEuler j (stepanovWordMoment L f g) =
      stepanovWordMoment (j :: L) f g +
        stepanovWordMoment L f (fun i => integralEuler j (g i)) := by
  simp only [stepanovWordMoment, map_sum, integralEuler_mul, sum_add_distrib,
    integralEulerWord_cons]

theorem integralEuler_stepanovAux {m : ℕ} (q : ℕ) (j : σ)
    (f g : Fin m → MvPolynomial σ ℤ) :
    integralEuler j (stepanovAux q f g) =
      stepanovAux q (fun i => integralEuler j (f i)) g +
        (q : ℤ) • stepanovAux q f (fun i => integralEuler j (g i)) := by
  simp only [stepanovAux, map_sum, integralEuler_mul, integralEuler_adams,
    sum_add_distrib, smul_sum, mul_smul_comm]

/-- Global first-factor syzygies force every mixed Euler jet through the same order. -/
theorem aeval_eulerWord_stepanov_eq_zero (q : ℕ) (L : List σ) (u : σ → ℂ)
    (hu : ∀ j, u j ^ q = u j) {m : ℕ} (f g : Fin m → MvPolynomial σ ℤ)
    (hsy : ∀ K : List σ, K.length ≤ L.length → stepanovWordMoment K f g = 0) :
    aeval u (integralEulerWord L (stepanovAux q f g)) = 0 := by
  induction L using List.reverseRecOn generalizing f g with
  | nil =>
    have h := congrArg (aeval u) (hsy [] (by simp))
    simpa only [integralEulerWord_nil, stepanovAux, stepanovWordMoment, map_sum,
      map_mul, aeval_adams_fixed q u hu, map_zero] using h
  | append_singleton L j ih =>
    rw [integralEulerWord_append, integralEulerWord_cons, integralEulerWord_nil,
      integralEuler_stepanovAux, map_add, map_zsmul, map_add, map_zsmul]
    have hf : ∀ K : List σ, K.length ≤ L.length →
        stepanovWordMoment K (fun i => integralEuler j (f i)) g = 0 := by
      intro K hK
      have h := hsy (K ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [stepanovWordMoment, integralEulerWord_append,
        integralEulerWord_cons, integralEulerWord_nil] using h
    have hg : ∀ K : List σ, K.length ≤ L.length →
        stepanovWordMoment K f (fun i => integralEuler j (g i)) = 0 := by
      intro K hK
      have hK0 := hsy K (by simp only [List.length_append, List.length_singleton]; omega)
      have hjK := hsy (j :: K) (by
        simp only [List.length_cons, List.length_append, List.length_singleton]; omega)
      have h := congrArg (integralEuler j) hK0
      rw [integralEuler_stepanovWordMoment, hjK, zero_add, map_zero] at h
      exact h
    rw [ih _ _ hf, ih _ _ hg, smul_zero, add_zero]

/-- Vanishing of all mixed Euler words below a uniform order. -/
def EulerVanishesToOrder (F : MvPolynomial σ ℤ) (u : σ → ℂ) (r : ℕ) : Prop :=
  ∀ L : List σ, L.length < r → aeval u (integralEulerWord L F) = 0

theorem eulerVanishesToOrder_stepanov (q r : ℕ) (u : σ → ℂ)
    (hu : ∀ j, u j ^ q = u j) {m : ℕ} (f g : Fin m → MvPolynomial σ ℤ)
    (hsy : ∀ L : List σ, L.length < r → stepanovWordMoment L f g = 0) :
    EulerVanishesToOrder (stepanovAux q f g) u r := by
  intro L hL
  exact aeval_eulerWord_stepanov_eq_zero q L u hu f g fun K hK => hsy K (lt_of_le_of_lt hK hL)

theorem EulerVanishesToOrder.mono {F : MvPolynomial σ ℤ} {u : σ → ℂ} {r s : ℕ}
    (h : EulerVanishesToOrder F u r) (hs : s ≤ r) : EulerVanishesToOrder F u s :=
  fun L hL => h L (lt_of_lt_of_le hL hs)

theorem EulerVanishesToOrder.sub {F G : MvPolynomial σ ℤ} {u : σ → ℂ} {r : ℕ}
    (hF : EulerVanishesToOrder F u r) (hG : EulerVanishesToOrder G u r) :
    EulerVanishesToOrder (F - G) u r := by
  intro L hL
  rw [map_sub, map_sub, hF L hL, hG L hL, sub_zero]

theorem eulerVanishesToOrder_succ_iff (F : MvPolynomial σ ℤ) (u : σ → ℂ) (r : ℕ) :
    EulerVanishesToOrder F u (r + 1) ↔
      aeval u F = 0 ∧ ∀ j, EulerVanishesToOrder (integralEuler j F) u r := by
  constructor
  · intro h
    refine ⟨h [] (by simp), ?_⟩
    intro j L hL
    have hv := h (L ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [integralEulerWord_append, integralEulerWord_cons, integralEulerWord_nil] using hv
  · rintro ⟨h0, hd⟩ L hL
    induction L using List.reverseRecOn with
    | nil => exact h0
    | append_singleton L j _ =>
      rw [integralEulerWord_append, integralEulerWord_cons, integralEulerWord_nil]
      exact hd j L (by simp only [List.length_append, List.length_singleton] at hL; omega)

/-- Multiplication by a coordinate nonzero at the point cannot hide an Euler jet. -/
theorem eulerVanishesToOrder_of_X_mul (i : σ) (u : σ → ℂ) (hi : u i ≠ 0) (r : ℕ)
    (F : MvPolynomial σ ℤ) (h : EulerVanishesToOrder (X i * F) u r) :
    EulerVanishesToOrder F u r := by
  induction r generalizing F with
  | zero => intro L hL; omega
  | succ r ih =>
    obtain ⟨h0, hd⟩ := (eulerVanishesToOrder_succ_iff _ _ _).mp h
    apply (eulerVanishesToOrder_succ_iff _ _ _).mpr
    rw [map_mul, aeval_X] at h0
    refine ⟨(mul_eq_zero.mp h0).resolve_left hi, ?_⟩
    intro j
    apply ih
    have hj := hd j
    by_cases hji : j = i
    · subst j
      have hs := hj.sub (h.mono (Nat.le_succ r))
      rw [integralEuler_mul, integralEuler_X_self] at hs
      have he : X i * F + X i * integralEuler i F - X i * F =
          X i * integralEuler i F := by ring
      rw [he] at hs
      exact hs
    · rw [integralEuler_mul, integralEuler_X_of_ne (Ne.symm hji), zero_mul, zero_add] at hj
      exact hj

/-- Nonzero coordinates convert mixed Euler vanishing into ordinary uniform multiplicity. -/
theorem vanishesToOrder_of_eulerVanishesToOrder (u : σ → ℂ) (hu : ∀ j, u j ≠ 0)
    (r : ℕ) (F : MvPolynomial σ ℤ) (h : EulerVanishesToOrder F u r) :
    VanishesToOrder F u r := by
  induction r generalizing F with
  | zero => intro L hL; omega
  | succ r ih =>
    obtain ⟨h0, hd⟩ := (eulerVanishesToOrder_succ_iff _ _ _).mp h
    have hp : ∀ j, VanishesToOrder (pderiv j F) u r := by
      intro j
      apply ih
      exact eulerVanishesToOrder_of_X_mul j u (hu j) r (pderiv j F) (hd j)
    intro L hL
    induction L using List.reverseRecOn with
    | nil => exact h0
    | append_singleton L j _ =>
      rw [← iterDeriv_pderiv]
      exact hp j L (by simp only [List.length_append, List.length_singleton] at hL; omega)

/-- Polynomial mixed syzygies force full ordinary multiplicity on the fixed torus. -/
theorem vanishesToOrder_stepanov_of_syzygies (q r : ℕ) (u : σ → ℂ)
    (hu : ∀ j, u j ^ q = u j) (hunit : ∀ j, u j ≠ 0) {m : ℕ}
    (f g : Fin m → MvPolynomial σ ℤ)
    (hsy : ∀ L : List σ, L.length < r → stepanovWordMoment L f g = 0) :
    VanishesToOrder (stepanovAux q f g) u r :=
  vanishesToOrder_of_eulerVanishesToOrder u hunit r _
    (eulerVanishesToOrder_stepanov q r u hu f g hsy)

/-- Exact syzygies retain the exponential arithmetic cost of characteristic-zero order. -/
theorem two_pow_le_length_stepanov_of_syzygies {P : Finset Nat.Primes} (q r : ℕ)
    (u : P → ℂ) (hu : ∀ j, u j ^ q = u j) (hunit : ∀ j, u j ≠ 0) {m : ℕ}
    (f g : Fin m → MvPolynomial P ℤ) (hne : stepanovAux q f g ≠ 0)
    (hsy : ∀ L : List P, L.length < r → stepanovWordMoment L f g = 0) :
    2 ^ r ≤ length (stepanovAux q f g) :=
  two_pow_le_length_of_vanishesToOrder hne
    (vanishesToOrder_stepanov_of_syzygies q r u hu hunit f g hsy)

#print axioms aeval_eulerWord_stepanov_eq_zero
#print axioms vanishesToOrder_stepanov_of_syzygies
#print axioms two_pow_le_length_stepanov_of_syzygies

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
