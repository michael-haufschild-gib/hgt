import GaloisForLFunctions.RHTower.XiCTaylorMovingSignedCompletionConditioningNoGo

/-!
# Four signed source atoms control the complete completion jet

Positivity forces a uniform half-plane logarithmic-current bound, and signed completions which
screen an Xi Taylor charge must be ill-conditioned.  This module proves the exact boundary of
those no-go theorems: after signs and mesh-dependent source locations are allowed, four atoms
already interpolate an arbitrary complex completion value and arbitrary complex first derivative.

At a point `z = π/(2T) + iy`, atoms at `T, 2T, 3T, 4T` have phases

`ir, -r², -ir³, r⁴`, where `r = exp(-Ty)`.

The resulting real `4 × 4` value--derivative system is nonsingular.  Explicit inverse weights
prove surjectivity without a determinant oracle.  A final specialization realizes any prescribed
horizontal logarithmic charge exactly.

This is not a source-only Xi construction: the last specialization deliberately places the
desired charge in the interpolated jet.  Its role is a sharp theatre boundary.  Pointwise
integrability, finite atomicity, and the two integration-by-parts source connections cannot
exclude a signed moving gauge.  Any further Route-J theorem must use cross-mesh source coherence
or source independence from the divisor datum.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Upper-half-plane point whose first source atom has quarter-turn phase. -/
def signedQuarterTurnPoint (T y : ℝ) : ℂ :=
  ⟨Real.pi / (2 * T), y⟩

theorem spectralTranslationPhase_quarterTurn_one
    {T : ℝ} (hT : T ≠ 0) (y : ℝ) :
    spectralTranslationPhase T (signedQuarterTurnPoint T y) =
      ⟨0, Real.exp (-T * y)⟩ := by
  apply Complex.ext
  · rw [spectralTranslationPhase, Complex.exp_re]
    simp [signedQuarterTurnPoint, mul_re, mul_im]
    field_simp [hT]
    exact Real.cos_pi_div_two
  · rw [spectralTranslationPhase, Complex.exp_im]
    simp [signedQuarterTurnPoint, mul_re, mul_im]
    field_simp [hT]
    exact Real.sin_pi_div_two

theorem spectralTranslationPhase_nat_mul
    (n : ℕ) (T : ℝ) (z : ℂ) :
    spectralTranslationPhase ((n : ℝ) * T) z =
      spectralTranslationPhase T z ^ n := by
  unfold spectralTranslationPhase
  rw [show ((((n : ℝ) * T : ℝ) : ℂ) * I) * z =
      (n : ℂ) * (((T : ℂ) * I) * z) by push_cast; ring,
    Complex.exp_nat_mul]

theorem spectralTranslationPhase_quarterTurn_two
    {T : ℝ} (hT : T ≠ 0) (y : ℝ) :
    spectralTranslationPhase (2 * T) (signedQuarterTurnPoint T y) =
      ⟨-(Real.exp (-T * y) ^ (2 : ℕ)), 0⟩ := by
  calc
    spectralTranslationPhase (2 * T) (signedQuarterTurnPoint T y) =
        spectralTranslationPhase T (signedQuarterTurnPoint T y) ^ (2 : ℕ) := by
      simpa using spectralTranslationPhase_nat_mul 2 T
        (signedQuarterTurnPoint T y)
    _ = _ := by
      rw [spectralTranslationPhase_quarterTurn_one hT]
      apply Complex.ext <;>
        norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

theorem spectralTranslationPhase_quarterTurn_three
    {T : ℝ} (hT : T ≠ 0) (y : ℝ) :
    spectralTranslationPhase (3 * T) (signedQuarterTurnPoint T y) =
      ⟨0, -(Real.exp (-T * y) ^ (3 : ℕ))⟩ := by
  calc
    spectralTranslationPhase (3 * T) (signedQuarterTurnPoint T y) =
        spectralTranslationPhase T (signedQuarterTurnPoint T y) ^ (3 : ℕ) := by
      simpa using spectralTranslationPhase_nat_mul 3 T
        (signedQuarterTurnPoint T y)
    _ = _ := by
      rw [spectralTranslationPhase_quarterTurn_one hT]
      apply Complex.ext <;>
        norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

theorem spectralTranslationPhase_quarterTurn_four
    {T : ℝ} (hT : T ≠ 0) (y : ℝ) :
    spectralTranslationPhase (4 * T) (signedQuarterTurnPoint T y) =
      ⟨Real.exp (-T * y) ^ (4 : ℕ), 0⟩ := by
  calc
    spectralTranslationPhase (4 * T) (signedQuarterTurnPoint T y) =
        spectralTranslationPhase T (signedQuarterTurnPoint T y) ^ (4 : ℕ) := by
      simpa using spectralTranslationPhase_nat_mul 4 T
        (signedQuarterTurnPoint T y)
    _ = _ := by
      rw [spectralTranslationPhase_quarterTurn_one hT]
      apply Complex.ext <;>
        norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

/-- Completion of four signed atoms at the quarter-turn source locations. -/
def signedFourAtomCompletion
    (T a₁ a₂ a₃ a₄ : ℝ) (z : ℂ) : ℂ :=
  (a₁ : ℂ) * (1 - spectralTranslationPhase T z) +
  (a₂ : ℂ) * (1 - spectralTranslationPhase (2 * T) z) +
  (a₃ : ℂ) * (1 - spectralTranslationPhase (3 * T) z) +
  (a₄ : ℂ) * (1 - spectralTranslationPhase (4 * T) z)

/-- First spectral derivative of the four-atom completion. -/
def signedFourAtomCompletionDerivative
    (T a₁ a₂ a₃ a₄ : ℝ) (z : ℂ) : ℂ :=
  (a₁ : ℂ) * (-((T : ℂ) * I) * spectralTranslationPhase T z) +
  (a₂ : ℂ) * (-(((2 * T : ℝ) : ℂ) * I) *
    spectralTranslationPhase (2 * T) z) +
  (a₃ : ℂ) * (-(((3 * T : ℝ) : ℂ) * I) *
    spectralTranslationPhase (3 * T) z) +
  (a₄ : ℂ) * (-(((4 * T : ℝ) : ℂ) * I) *
    spectralTranslationPhase (4 * T) z)

/-- Real-coordinate form of the completion at a quarter-turn point. -/
def signedQuarterTurnCompletion
    (r a₁ a₂ a₃ a₄ : ℝ) : ℂ :=
  ⟨a₁ + (1 + r ^ (2 : ℕ)) * a₂ + a₃ + (1 - r ^ (4 : ℕ)) * a₄,
    -r * a₁ + r ^ (3 : ℕ) * a₃⟩

/-- Real-coordinate form of the derivative at a quarter-turn point. -/
def signedQuarterTurnCompletionDerivative
    (T r a₁ a₂ a₃ a₄ : ℝ) : ℂ :=
  ⟨T * r * a₁ - 3 * T * r ^ (3 : ℕ) * a₃,
    2 * T * r ^ (2 : ℕ) * a₂ - 4 * T * r ^ (4 : ℕ) * a₄⟩

theorem signedFourAtomCompletion_quarterTurn_eq
    {T : ℝ} (hT : T ≠ 0) (y a₁ a₂ a₃ a₄ : ℝ) :
    signedFourAtomCompletion T a₁ a₂ a₃ a₄
        (signedQuarterTurnPoint T y) =
      signedQuarterTurnCompletion (Real.exp (-T * y)) a₁ a₂ a₃ a₄ := by
  rw [signedFourAtomCompletion,
    spectralTranslationPhase_quarterTurn_one hT,
    spectralTranslationPhase_quarterTurn_two hT,
    spectralTranslationPhase_quarterTurn_three hT,
    spectralTranslationPhase_quarterTurn_four hT]
  apply Complex.ext <;>
    simp [signedQuarterTurnCompletion, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem signedFourAtomCompletionDerivative_quarterTurn_eq
    {T : ℝ} (hT : T ≠ 0) (y a₁ a₂ a₃ a₄ : ℝ) :
    signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄
        (signedQuarterTurnPoint T y) =
      signedQuarterTurnCompletionDerivative T (Real.exp (-T * y))
        a₁ a₂ a₃ a₄ := by
  rw [signedFourAtomCompletionDerivative,
    spectralTranslationPhase_quarterTurn_one hT,
    spectralTranslationPhase_quarterTurn_two hT,
    spectralTranslationPhase_quarterTurn_three hT,
    spectralTranslationPhase_quarterTurn_four hT]
  apply Complex.ext <;>
    simp [signedQuarterTurnCompletionDerivative,
      Complex.mul_re, Complex.mul_im] <;>
    ring

/-- First odd-block inverse coordinate. -/
def signedQuarterTurnWeightOne
    (T r : ℝ) (G H : ℂ) : ℝ :=
  -(3 * T * G.im + H.re) / (2 * T * r)

/-- Second odd-block inverse coordinate. -/
def signedQuarterTurnWeightThree
    (T r : ℝ) (G H : ℂ) : ℝ :=
  -(T * G.im + H.re) / (2 * T * r ^ (3 : ℕ))

def signedQuarterTurnRealResidual
    (T r : ℝ) (G H : ℂ) : ℝ :=
  G.re -
    signedQuarterTurnWeightOne T r G H -
    signedQuarterTurnWeightThree T r G H

/-- Second even-block inverse coordinate. -/
def signedQuarterTurnWeightFour
    (T r : ℝ) (G H : ℂ) : ℝ :=
  (signedQuarterTurnRealResidual T r G H -
      (1 + r ^ (2 : ℕ)) * H.im / (2 * T * r ^ (2 : ℕ))) /
    (1 + r ^ (2 : ℕ)) ^ (2 : ℕ)

/-- First even-block inverse coordinate. -/
def signedQuarterTurnWeightTwo
    (T r : ℝ) (G H : ℂ) : ℝ :=
  H.im / (2 * T * r ^ (2 : ℕ)) +
    2 * r ^ (2 : ℕ) * signedQuarterTurnWeightFour T r G H

/-- The four real quarter-turn weights control an arbitrary complex value and derivative. -/
theorem signedQuarterTurnCompletionJet_surjective
    {T r : ℝ} (hT : T ≠ 0) (hr : r ≠ 0) (G H : ℂ) :
    signedQuarterTurnCompletion r
        (signedQuarterTurnWeightOne T r G H)
        (signedQuarterTurnWeightTwo T r G H)
        (signedQuarterTurnWeightThree T r G H)
        (signedQuarterTurnWeightFour T r G H) = G ∧
      signedQuarterTurnCompletionDerivative T r
        (signedQuarterTurnWeightOne T r G H)
        (signedQuarterTurnWeightTwo T r G H)
        (signedQuarterTurnWeightThree T r G H)
        (signedQuarterTurnWeightFour T r G H) = H := by
  have hsq : 1 + r ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r]
  constructor <;>
    apply Complex.ext <;>
    simp [signedQuarterTurnCompletion,
      signedQuarterTurnCompletionDerivative,
      signedQuarterTurnWeightOne, signedQuarterTurnWeightTwo,
      signedQuarterTurnWeightThree, signedQuarterTurnWeightFour,
      signedQuarterTurnRealResidual] <;>
    field_simp [hT, hr, hsq] <;>
    ring

/-- Literal four-atom version of complete real-linear jet controllability. -/
theorem signedFourAtomCompletionJet_surjective
    {T : ℝ} (hT : T ≠ 0) (y : ℝ) (G H : ℂ) :
    ∃ a₁ a₂ a₃ a₄ : ℝ,
      signedFourAtomCompletion T a₁ a₂ a₃ a₄
          (signedQuarterTurnPoint T y) = G ∧
        signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄
          (signedQuarterTurnPoint T y) = H := by
  let r : ℝ := Real.exp (-T * y)
  have hr : r ≠ 0 := (Real.exp_pos _).ne'
  let a₁ := signedQuarterTurnWeightOne T r G H
  let a₂ := signedQuarterTurnWeightTwo T r G H
  let a₃ := signedQuarterTurnWeightThree T r G H
  let a₄ := signedQuarterTurnWeightFour T r G H
  refine ⟨a₁, a₂, a₃, a₄, ?_, ?_⟩
  · rw [signedFourAtomCompletion_quarterTurn_eq hT]
    simpa only [r, a₁, a₂, a₃, a₄] using
      (signedQuarterTurnCompletionJet_surjective hT hr G H).1
  · rw [signedFourAtomCompletionDerivative_quarterTurn_eq hT]
    simpa only [r, a₁, a₂, a₃, a₄] using
      (signedQuarterTurnCompletionJet_surjective hT hr G H).2

/-- Source value determined by `G = -izF`. -/
def atomicSourceConnectionValue (G z : ℂ) : ℂ :=
  I * G / z

/-- Source derivative determined by `H = -i(F+zD)`. -/
def atomicSourceConnectionDerivative (G H z : ℂ) : ℂ :=
  (I * H - atomicSourceConnectionValue G z) / z

theorem atomicSourceConnectionValue_eq
    {G z : ℂ} (hz : z ≠ 0) :
    G = -I * z * atomicSourceConnectionValue G z := by
  rw [atomicSourceConnectionValue]
  field_simp
  rw [I_sq]
  ring

theorem atomicSourceConnectionDerivative_eq
    {G H z : ℂ} (hz : z ≠ 0) :
    H = -I * (atomicSourceConnectionValue G z +
      z * atomicSourceConnectionDerivative G H z) := by
  rw [atomicSourceConnectionDerivative]
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem atomicSourceConnection_logDerivative_eq
    {G H z : ℂ} (hG : G ≠ 0) (hz : z ≠ 0) :
    atomicSourceConnectionDerivative G H z /
        atomicSourceConnectionValue G z =
      H / G - 1 / z := by
  rw [atomicSourceConnectionDerivative, atomicSourceConnectionValue]
  field_simp

/-- Four signed atoms realize any prescribed horizontal logarithmic charge exactly. -/
theorem exists_signedFourAtomCompletion_exact_horizontalCharge
    {T : ℝ} (hT : 0 < T) (y m : ℝ) :
    ∃ a₁ a₂ a₃ a₄ : ℝ,
      let z := signedQuarterTurnPoint T y
      let x := Real.pi / (2 * T)
      let G : ℂ := x
      let H : ℂ := I * (m + x * (1 / z).im)
      let F := atomicSourceConnectionValue G z
      let D := atomicSourceConnectionDerivative G H z
      signedFourAtomCompletion T a₁ a₂ a₃ a₄ z = -I * z * F ∧
        signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ z =
          -I * (F + z * D) ∧
        F ≠ 0 ∧
        x * (D / F).im = m := by
  have hT0 : T ≠ 0 := hT.ne'
  let z := signedQuarterTurnPoint T y
  let x := Real.pi / (2 * T)
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hz : z ≠ 0 := by
    intro hz0
    have : z.re = 0 := by rw [hz0]; rfl
    have hzre : z.re = x := rfl
    linarith
  let G : ℂ := x
  let H : ℂ := I * (m + x * (1 / z).im)
  obtain ⟨a₁, a₂, a₃, a₄, hG, hH⟩ :=
    signedFourAtomCompletionJet_surjective hT0 y G H
  refine ⟨a₁, a₂, a₃, a₄, ?_, ?_, ?_, ?_⟩
  · exact hG.trans (atomicSourceConnectionValue_eq hz)
  · exact hH.trans (atomicSourceConnectionDerivative_eq hz)
  · rw [atomicSourceConnectionValue]
    exact div_ne_zero (mul_ne_zero I_ne_zero hx0) hz
  · rw [atomicSourceConnection_logDerivative_eq hx0 hz]
    have hI :
        (I * ((m : ℂ) + (x : ℂ) * ((1 / z).im : ℂ)) / (x : ℂ)).im =
        (m + x * (1 / z).im) / x := by
      rw [Complex.div_im]
      simp only [mul_im, I_re, add_im, ofReal_im, mul_zero, add_zero,
        I_im, add_re, ofReal_re, zero_mul, one_mul, mul_re,
        normSq_apply]
      field_simp [hx.ne']
      ring
    rw [sub_im]
    change x *
      ((I * ((m : ℂ) + (x : ℂ) * ((1 / z).im : ℂ)) / (x : ℂ)).im -
        (1 / z).im) = m
    rw [hI]
    field_simp [hx.ne']
    ring

theorem signedQuarterTurnPoint_reconstruct
    {z : ℂ} (hzre : 0 < z.re) :
    signedQuarterTurnPoint (Real.pi / (2 * z.re)) z.im = z := by
  apply Complex.ext
  · simp only [signedQuarterTurnPoint]
    field_simp [Real.pi_ne_zero, hzre.ne']
  · rfl

/-- Pointwise universality on every right upper-half-plane mesh point. -/
theorem exists_signedFourAtomCompletion_exact_horizontalChargeAt
    {z : ℂ} (hzre : 0 < z.re) (m : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∃ a₁ a₂ a₃ a₄ : ℝ,
        let G : ℂ := z.re
        let H : ℂ := I * (m + z.re * (1 / z).im)
        let F := atomicSourceConnectionValue G z
        let D := atomicSourceConnectionDerivative G H z
        signedFourAtomCompletion T a₁ a₂ a₃ a₄ z = -I * z * F ∧
          signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ z =
            -I * (F + z * D) ∧
          F ≠ 0 ∧
          z.re * (D / F).im = m := by
  let T : ℝ := Real.pi / (2 * z.re)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hpoint : signedQuarterTurnPoint T z.im = z := by
    simpa only [T] using signedQuarterTurnPoint_reconstruct hzre
  have hxpoint : Real.pi / (2 * T) = z.re := by
    have := congrArg Complex.re hpoint
    simpa only [signedQuarterTurnPoint] using this
  obtain ⟨a₁, a₂, a₃, a₄, hcompletion, hderivative, hF, hcharge⟩ :=
    exists_signedFourAtomCompletion_exact_horizontalCharge hT z.im m
  refine ⟨T, hT, a₁, a₂, a₃, a₄, ?_, ?_, ?_, ?_⟩
  · simpa only [hpoint, hxpoint] using hcompletion
  · simpa only [hpoint, hxpoint] using hderivative
  · simpa only [hpoint, hxpoint] using hF
  · simpa only [hpoint, hxpoint] using hcharge

/-- Strong scaled form: the prescribed charge scale is independent of the completion point.
Keeping `G = 1` makes the required derivative jet grow exactly like `1 / δ`. -/
theorem exists_signedFourAtomCompletion_exact_scaledCharge
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (y m : ℝ) :
    ∃ a₁ a₂ a₃ a₄ : ℝ,
      let z := signedQuarterTurnPoint T y
      let G : ℂ := 1
      let H : ℂ := I * (m / δ + (1 / z).im)
      let F := atomicSourceConnectionValue G z
      let D := atomicSourceConnectionDerivative G H z
      signedFourAtomCompletion T a₁ a₂ a₃ a₄ z = -I * z * F ∧
        signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ z =
          -I * (F + z * D) ∧
        F ≠ 0 ∧
        δ * (D / F).im = m := by
  have hT0 : T ≠ 0 := hT.ne'
  let z := signedQuarterTurnPoint T y
  have hz : z ≠ 0 := by
    intro hz0
    have hzre : z.re = 0 := by rw [hz0]; rfl
    have hzrePos : 0 < z.re := by
      dsimp only [z, signedQuarterTurnPoint]
      positivity
    linarith
  let G : ℂ := 1
  let H : ℂ := I * (m / δ + (1 / z).im)
  obtain ⟨a₁, a₂, a₃, a₄, hG, hH⟩ :=
    signedFourAtomCompletionJet_surjective hT0 y G H
  refine ⟨a₁, a₂, a₃, a₄, ?_, ?_, ?_, ?_⟩
  · exact hG.trans (atomicSourceConnectionValue_eq hz)
  · exact hH.trans (atomicSourceConnectionDerivative_eq hz)
  · rw [atomicSourceConnectionValue]
    exact div_ne_zero (mul_ne_zero I_ne_zero one_ne_zero) hz
  · rw [atomicSourceConnection_logDerivative_eq one_ne_zero hz]
    rw [div_one, sub_im]
    change δ *
      ((I * ((m : ℂ) / (δ : ℂ) + ((1 / z).im : ℂ))).im -
        (1 / z).im) = m
    simp only [mul_im, I_re, div_im, ofReal_im, mul_zero, zero_div,
      zero_sub, zero_mul, I_im, add_re, div_re, ofReal_re, one_mul,
      add_im, normSq_apply]
    field_simp [hδ.ne']
    ring

/-- Every right-half-plane completion point admits exact interpolation at any independent positive
mesh scale.  This is the form used to show sharpness of the Xi signed-conditioning barrier. -/
theorem exists_signedFourAtomCompletion_exact_scaledChargeAt
    {z : ℂ} (hzre : 0 < z.re) {δ : ℝ} (hδ : 0 < δ) (m : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∃ a₁ a₂ a₃ a₄ : ℝ,
        let G : ℂ := 1
        let H : ℂ := I * (m / δ + (1 / z).im)
        let F := atomicSourceConnectionValue G z
        let D := atomicSourceConnectionDerivative G H z
        signedFourAtomCompletion T a₁ a₂ a₃ a₄ z = -I * z * F ∧
          signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ z =
            -I * (F + z * D) ∧
          F ≠ 0 ∧
          δ * (D / F).im = m := by
  let T : ℝ := Real.pi / (2 * z.re)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hpoint : signedQuarterTurnPoint T z.im = z := by
    simpa only [T] using signedQuarterTurnPoint_reconstruct hzre
  obtain ⟨a₁, a₂, a₃, a₄, hcompletion, hderivative, hF, hcharge⟩ :=
    exists_signedFourAtomCompletion_exact_scaledCharge hT hδ z.im m
  refine ⟨T, hT, a₁, a₂, a₃, a₄, ?_, ?_, ?_, ?_⟩
  · simpa only [hpoint] using hcompletion
  · simpa only [hpoint] using hderivative
  · simpa only [hpoint] using hF
  · simpa only [hpoint] using hcharge

/-- Exact pointwise signed-atomic screening predicate at an externally supplied mesh scale. -/
def SignedFourAtomCompletionExactScaledChargeAt
    (z : ℂ) (δ m : ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧
    ∃ a₁ a₂ a₃ a₄ : ℝ,
      let G : ℂ := 1
      let H : ℂ := I * (m / δ + (1 / z).im)
      let F := atomicSourceConnectionValue G z
      let D := atomicSourceConnectionDerivative G H z
      signedFourAtomCompletion T a₁ a₂ a₃ a₄ z = -I * z * F ∧
        signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ z =
          -I * (F + z * D) ∧
        F ≠ 0 ∧
        δ * (D / F).im = m

theorem signedFourAtomCompletionExactScaledChargeAt
    {z : ℂ} (hzre : 0 < z.re) {δ : ℝ} (hδ : 0 < δ) (m : ℝ) :
    SignedFourAtomCompletionExactScaledChargeAt z δ m :=
  exists_signedFourAtomCompletion_exact_scaledChargeAt hzre hδ m

/-- On every positive-ordinate Xi anisotropic mesh, target-fitted signed four-atom packets realize
any prescribed charge exactly at all sufficiently large stages.  This proves sharpness of the
pointwise signed-conditioning obstruction; the witnesses are deliberately not source-independent. -/
theorem eventually_signedFourAtomCompletionExactScaledChargeAt_xiMesh
    {sigma : ℂ} (hsigmaIm : 0 < sigma.im) (m : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      SignedFourAtomCompletionExactScaledChargeAt
        (xiCTaylorAnisotropicCenteredPoint sigma n)
        (xiTaylorAnisotropicHorizontalStep sigma n) m := by
  have hcenterRe :
      (xiCTaylorCenteredPoint sigma).re = sigma.im := by
    dsimp only [xiCTaylorCenteredPoint]
    rw [mul_re]
    simp
  have hreTend : Filter.Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).re)
      Filter.atTop (nhds sigma.im) := by
    have h :=
      Complex.continuous_re.continuousAt.tendsto.comp
        (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
    simpa [Function.comp_def, hcenterRe] using h
  have hre : ∀ᶠ n : ℕ in Filter.atTop,
      0 < (xiCTaylorAnisotropicCenteredPoint sigma n).re :=
    hreTend.eventually (eventually_gt_nhds hsigmaIm)
  filter_upwards [hre] with n hzn
  have hstepBounds :=
    xiTaylorAnisotropicRightApprox_re_sub_bounds sigma (Nat.succ_pos n)
  have hδ : 0 < xiTaylorAnisotropicHorizontalStep sigma n := by
    dsimp only [xiTaylorAnisotropicHorizontalStep]
    exact lt_of_lt_of_le (by positivity) hstepBounds.1
  exact signedFourAtomCompletionExactScaledChargeAt hzn hδ m

/-- Weight at the fourth quarter turn in the unique even-channel solution of the scalar
value/derivative interpolation problem. -/
def signedEvenQuarterTurnWeightFour
    (T r q : ℝ) : ℝ :=
  (1 - (1 + r ^ (2 : ℕ)) * q / (2 * T * r ^ (2 : ℕ))) /
    (1 + r ^ (2 : ℕ)) ^ (2 : ℕ)

/-- Weight at the second quarter turn in the unique even-channel solution of the scalar
value/derivative interpolation problem. -/
def signedEvenQuarterTurnWeightTwo
    (T r q : ℝ) : ℝ :=
  q / (2 * T * r ^ (2 : ℕ)) +
    2 * r ^ (2 : ℕ) * signedEvenQuarterTurnWeightFour T r q

/-- Two even quarter-turn atoms realize every real derivative target while fixing the completion
value at one. -/
theorem signedEvenQuarterTurnCompletionJet_eq
    {T r : ℝ} (hT : T ≠ 0) (hr : r ≠ 0) (q : ℝ) :
    signedQuarterTurnCompletion r 0
        (signedEvenQuarterTurnWeightTwo T r q) 0
        (signedEvenQuarterTurnWeightFour T r q) = 1 ∧
      signedQuarterTurnCompletionDerivative T r 0
        (signedEvenQuarterTurnWeightTwo T r q) 0
        (signedEvenQuarterTurnWeightFour T r q) = I * (q : ℂ) := by
  have hsq : 1 + r ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r]
  constructor <;>
    apply Complex.ext <;>
    simp [signedQuarterTurnCompletion,
      signedQuarterTurnCompletionDerivative,
      signedEvenQuarterTurnWeightTwo,
      signedEvenQuarterTurnWeightFour] <;>
    field_simp [hT, hr, hsq] <;>
    ring

/-- The two even quarter-turn weights are forced by the scalar jet.  Thus exact scalar charge
screening has no hidden finite-dimensional freedom inside this channel. -/
theorem signedEvenQuarterTurnCompletionJet_unique
    {T r a₂ a₄ q : ℝ} (hT : T ≠ 0) (hr : r ≠ 0)
    (hG : signedQuarterTurnCompletion r 0 a₂ 0 a₄ = 1)
    (hH : signedQuarterTurnCompletionDerivative T r 0 a₂ 0 a₄ =
      I * (q : ℂ)) :
    a₂ = signedEvenQuarterTurnWeightTwo T r q ∧
      a₄ = signedEvenQuarterTurnWeightFour T r q := by
  have hsq : 1 + r ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r]
  have hGre := congrArg Complex.re hG
  have hHim := congrArg Complex.im hH
  simp only [signedQuarterTurnCompletion,
    signedQuarterTurnCompletionDerivative, one_re,
    mul_im, I_re, ofReal_im, zero_mul, I_im, ofReal_re, one_mul] at hGre hHim
  have ha₄ : a₄ = signedEvenQuarterTurnWeightFour T r q := by
    simp only [signedEvenQuarterTurnWeightFour]
    field_simp [hT, hr, hsq]
    linear_combination
      (2 * T * r ^ (2 : ℕ)) * hGre - (1 + r ^ (2 : ℕ)) * hHim
  have ha₂ : a₂ = signedEvenQuarterTurnWeightTwo T r q := by
    rw [signedEvenQuarterTurnWeightTwo, ← ha₄]
    field_simp [hT, hr]
    linarith
  exact ⟨ha₂, ha₄⟩

/-- A scalar jet `(1,iq)` has no odd-channel component.  Hence the four-atom inverse collapses
canonically to the two even atoms, rather than merely admitting a two-atom representative. -/
theorem signedQuarterTurnScalarJet_odd_weights_eq_zero
    {T r a₁ a₂ a₃ a₄ q : ℝ} (hT : T ≠ 0) (hr : r ≠ 0)
    (hG : signedQuarterTurnCompletion r a₁ a₂ a₃ a₄ = 1)
    (hH : signedQuarterTurnCompletionDerivative T r a₁ a₂ a₃ a₄ =
      I * (q : ℂ)) :
    a₁ = 0 ∧ a₃ = 0 := by
  have hGim := congrArg Complex.im hG
  have hHre := congrArg Complex.re hH
  simp [signedQuarterTurnCompletion,
    signedQuarterTurnCompletionDerivative] at hGim hHre
  have ha₃prod : (-2 * T * r ^ (3 : ℕ)) * a₃ = 0 := by
    linear_combination hHre + T * hGim
  have ha₃coeff : -2 * T * r ^ (3 : ℕ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) hT)
      (pow_ne_zero 3 hr)
  have ha₃ : a₃ = 0 :=
    (mul_eq_zero.mp ha₃prod).resolve_left ha₃coeff
  have ha₁prod : (-r) * a₁ = 0 := by
    rw [ha₃, mul_zero, add_zero] at hGim
    simpa only [neg_mul] using hGim
  have ha₁ : a₁ = 0 :=
    (mul_eq_zero.mp ha₁prod).resolve_left (neg_ne_zero.mpr hr)
  exact ⟨ha₁, ha₃⟩

/-- Complete uniqueness for a scalar charge jet: its odd weights vanish and its two even weights
are the explicit inverse coordinates. -/
theorem signedQuarterTurnScalarJet_unique
    {T r a₁ a₂ a₃ a₄ q : ℝ} (hT : T ≠ 0) (hr : r ≠ 0)
    (hG : signedQuarterTurnCompletion r a₁ a₂ a₃ a₄ = 1)
    (hH : signedQuarterTurnCompletionDerivative T r a₁ a₂ a₃ a₄ =
      I * (q : ℂ)) :
    a₁ = 0 ∧
      a₂ = signedEvenQuarterTurnWeightTwo T r q ∧
      a₃ = 0 ∧
      a₄ = signedEvenQuarterTurnWeightFour T r q := by
  obtain ⟨ha₁, ha₃⟩ :=
    signedQuarterTurnScalarJet_odd_weights_eq_zero hT hr hG hH
  have hGeven :
      signedQuarterTurnCompletion r 0 a₂ 0 a₄ = 1 := by
    simpa only [ha₁, ha₃] using hG
  have hHeven :
      signedQuarterTurnCompletionDerivative T r 0 a₂ 0 a₄ =
        I * (q : ℂ) := by
    simpa only [ha₁, ha₃] using hH
  obtain ⟨ha₂, ha₄⟩ :=
    signedEvenQuarterTurnCompletionJet_unique hT hr hGeven hHeven
  exact ⟨ha₁, ha₂, ha₃, ha₄⟩

/-- At a literal quarter-turn point, two even atoms already realize the scalar jet `(1, iq)`. -/
theorem signedTwoEvenAtomCompletionJet
    {T : ℝ} (hT : T ≠ 0) (y q : ℝ) :
    ∃ a₂ a₄ : ℝ,
      signedFourAtomCompletion T 0 a₂ 0 a₄
          (signedQuarterTurnPoint T y) = 1 ∧
        signedFourAtomCompletionDerivative T 0 a₂ 0 a₄
          (signedQuarterTurnPoint T y) = I * (q : ℂ) := by
  let r : ℝ := Real.exp (-T * y)
  have hr : r ≠ 0 := (Real.exp_pos _).ne'
  let a₂ := signedEvenQuarterTurnWeightTwo T r q
  let a₄ := signedEvenQuarterTurnWeightFour T r q
  refine ⟨a₂, a₄, ?_, ?_⟩
  · rw [signedFourAtomCompletion_quarterTurn_eq hT]
    simpa only [r, a₂, a₄] using
      (signedEvenQuarterTurnCompletionJet_eq hT hr q).1
  · rw [signedFourAtomCompletionDerivative_quarterTurn_eq hT]
    simpa only [r, a₂, a₄] using
      (signedEvenQuarterTurnCompletionJet_eq hT hr q).2

/-- Exact horizontal charge is a two-even-atom phenomenon.  The target-fitted weights are unique,
so all cross-mesh coherence information is carried by their explicit amplitudes. -/
theorem exists_signedTwoEvenAtomCompletion_exact_scaledCharge
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (y m : ℝ) :
    ∃ a₂ a₄ : ℝ,
      let z := signedQuarterTurnPoint T y
      let G : ℂ := 1
      let H : ℂ := I * ((m / δ + (1 / z).im : ℝ) : ℂ)
      let F := atomicSourceConnectionValue G z
      let D := atomicSourceConnectionDerivative G H z
      signedFourAtomCompletion T 0 a₂ 0 a₄ z = -I * z * F ∧
        signedFourAtomCompletionDerivative T 0 a₂ 0 a₄ z =
          -I * (F + z * D) ∧
        F ≠ 0 ∧
        δ * (D / F).im = m := by
  have hT0 : T ≠ 0 := hT.ne'
  let z := signedQuarterTurnPoint T y
  have hz : z ≠ 0 := by
    intro hz0
    have hzre : z.re = 0 := by rw [hz0]; rfl
    have hzrePos : 0 < z.re := by
      dsimp only [z, signedQuarterTurnPoint]
      positivity
    linarith
  let q : ℝ := m / δ + (1 / z).im
  obtain ⟨a₂, a₄, hG, hH⟩ :=
    signedTwoEvenAtomCompletionJet hT0 y q
  refine ⟨a₂, a₄, ?_, ?_, ?_, ?_⟩
  · exact hG.trans (atomicSourceConnectionValue_eq hz)
  · change signedFourAtomCompletionDerivative T 0 a₂ 0 a₄ z =
      -I * (atomicSourceConnectionValue 1 z +
        z * atomicSourceConnectionDerivative 1 (I * (q : ℂ)) z)
    exact hH.trans
      (atomicSourceConnectionDerivative_eq
        (G := 1) (H := I * (q : ℂ)) hz)
  · rw [atomicSourceConnectionValue]
    exact div_ne_zero (mul_ne_zero I_ne_zero one_ne_zero) hz
  · rw [atomicSourceConnection_logDerivative_eq one_ne_zero hz]
    rw [div_one, sub_im]
    change δ *
      ((I * ((m / δ + (1 / z).im : ℝ) : ℂ)).im -
        (1 / z).im) = m
    simp only [mul_im, I_re, div_im, ofReal_im, mul_zero, I_im,
      ofReal_re, one_mul, normSq_apply]
    field_simp [hδ.ne']
    ring

/-- The value normalization alone forces the exact projective line containing every even-channel
weight pair.  Charge changes position along this line, but cannot change its direction. -/
theorem signedEvenQuarterTurnValueFingerprint
    {r a₂ a₄ : ℝ}
    (hG : signedQuarterTurnCompletion r 0 a₂ 0 a₄ = 1) :
    a₂ + (1 - r ^ (2 : ℕ)) * a₄ = 1 / (1 + r ^ (2 : ℕ)) := by
  have hden : 1 + r ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r]
  have hGre := congrArg Complex.re hG
  simp [signedQuarterTurnCompletion] at hGre
  apply (eq_div_iff hden).2
  linear_combination hGre

/-- After multiplication by mesh width, the affine value line collapses onto the projective charge
ray at the exact rate `δ / (1+r²)`. -/
theorem signedEvenQuarterTurnScaledValueFingerprint
    {δ r a₂ a₄ : ℝ}
    (hG : signedQuarterTurnCompletion r 0 a₂ 0 a₄ = 1) :
    δ * a₂ + (1 - r ^ (2 : ℕ)) * (δ * a₄) =
      δ / (1 + r ^ (2 : ℕ)) := by
  have h := signedEvenQuarterTurnValueFingerprint hG
  calc
    δ * a₂ + (1 - r ^ (2 : ℕ)) * (δ * a₄) =
        δ * (a₂ + (1 - r ^ (2 : ℕ)) * a₄) := by ring
    _ = δ * (1 / (1 + r ^ (2 : ℕ))) := by rw [h]
    _ = δ / (1 + r ^ (2 : ℕ)) := by
      simp only [div_eq_mul_inv, one_mul]

/-- Any nontrivial normalized limit of exact even-channel screens remembers the geometric radius:
its limiting coordinates lie on the ray `b₂ + (1-r∞²)b₄ = 0`. -/
theorem tendsto_signedEvenQuarterTurn_projectiveFingerprint
    {δ r a₂ a₄ : ℕ → ℝ} {r₀ b₂ b₄ : ℝ}
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hr : Filter.Tendsto r Filter.atTop (nhds r₀))
    (hb₂ : Filter.Tendsto (fun n => δ n * a₂ n)
      Filter.atTop (nhds b₂))
    (hb₄ : Filter.Tendsto (fun n => δ n * a₄ n)
      Filter.atTop (nhds b₄))
    (hG : ∀ n : ℕ,
      signedQuarterTurnCompletion (r n) 0 (a₂ n) 0 (a₄ n) = 1) :
    b₂ + (1 - r₀ ^ (2 : ℕ)) * b₄ = 0 := by
  have hleft : Filter.Tendsto
      (fun n => δ n * a₂ n +
        (1 - (r n) ^ (2 : ℕ)) * (δ n * a₄ n))
      Filter.atTop (nhds (b₂ + (1 - r₀ ^ (2 : ℕ)) * b₄)) :=
    hb₂.add ((tendsto_const_nhds.sub (hr.pow 2)).mul hb₄)
  have hden : 1 + r₀ ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r₀]
  have hright : Filter.Tendsto
      (fun n => δ n / (1 + (r n) ^ (2 : ℕ)))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (δ / (fun n => 1 + (r n) ^ (2 : ℕ))) Filter.atTop (nhds 0)
    simpa only [zero_div] using
      hδ.div (tendsto_const_nhds.add (hr.pow 2)) hden
  have heq :
      (fun n => δ n * a₂ n +
        (1 - (r n) ^ (2 : ℕ)) * (δ n * a₄ n)) =
      (fun n => δ n / (1 + (r n) ^ (2 : ℕ))) := by
    funext n
    exact signedEvenQuarterTurnScaledValueFingerprint (hG n)
  have hleftZero : Filter.Tendsto
      (fun n => δ n * a₂ n +
        (1 - (r n) ^ (2 : ℕ)) * (δ n * a₄ n))
      Filter.atTop (nhds 0) := by
    rw [heq]
    exact hright
  exact tendsto_nhds_unique hleft hleftZero

/-- A common nonzero normalized fourth weight cannot screen two distinct positive radii.  This is
the cross-fibre rigidity missing from pointwise jet surjectivity. -/
theorem common_signedEvenQuarterTurn_projectiveFingerprint_rigid
    {r s b₂ b₄ : ℝ} (hr : 0 < r) (hs : 0 < s) (hb₄ : b₄ ≠ 0)
    (hray : b₂ + (1 - r ^ (2 : ℕ)) * b₄ = 0)
    (hsay : b₂ + (1 - s ^ (2 : ℕ)) * b₄ = 0) :
    r = s := by
  have hprod : (s ^ (2 : ℕ) - r ^ (2 : ℕ)) * b₄ = 0 := by
    linear_combination hray - hsay
  have hsquare : s ^ (2 : ℕ) - r ^ (2 : ℕ) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hb₄
  nlinarith

/-- Equality of projective directions, rather than equality of normalized representatives, is
already rigid.  This absorbs different positive mesh normalizations at two fibres. -/
theorem proportional_signedEvenQuarterTurn_projectiveFingerprint_rigid
    {r s b₂ b₄ c₂ c₄ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hb₄ : b₄ ≠ 0) (hc₄ : c₄ ≠ 0)
    (hray : b₂ + (1 - r ^ (2 : ℕ)) * b₄ = 0)
    (hsay : c₂ + (1 - s ^ (2 : ℕ)) * c₄ = 0)
    (hprojective : b₂ * c₄ = c₂ * b₄) :
    r = s := by
  have hb₂ : b₂ = -(1 - r ^ (2 : ℕ)) * b₄ := by linarith
  have hc₂ : c₂ = -(1 - s ^ (2 : ℕ)) * c₄ := by linarith
  rw [hb₂, hc₂] at hprojective
  have hprod : (r ^ (2 : ℕ) - s ^ (2 : ℕ)) * (b₄ * c₄) = 0 := by
    calc
      (r ^ (2 : ℕ) - s ^ (2 : ℕ)) * (b₄ * c₄) =
          (-(1 - r ^ (2 : ℕ)) * b₄) * c₄ -
            (-(1 - s ^ (2 : ℕ)) * c₄) * b₄ := by ring
      _ = 0 := sub_eq_zero.mpr hprojective
  have hsquare : r ^ (2 : ℕ) - s ^ (2 : ℕ) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (mul_ne_zero hb₄ hc₄)
  nlinarith

/-- Quarter-turn damping radius attached to a centered source-evaluation point. -/
def xiSignedAtomicQuarterTurnRadiusAt (z : ℂ) : ℝ :=
  Real.exp (-(Real.pi / (2 * z.re) * z.im))

/-- Limiting quarter-turn radius at the Xi fibre `sigma`. -/
def xiSignedAtomicLimitRadius (sigma : ℂ) : ℝ :=
  Real.exp (-(Real.pi / (2 * sigma.im) * (1 / 2 - sigma.re)))

theorem xiCTaylorCenteredPoint_re (sigma : ℂ) :
    (xiCTaylorCenteredPoint sigma).re = sigma.im := by
  rw [xiCTaylorCenteredPoint, mul_re]
  simp

theorem xiCTaylorCenteredPoint_im (sigma : ℂ) :
    (xiCTaylorCenteredPoint sigma).im = 1 / 2 - sigma.re := by
  rw [xiCTaylorCenteredPoint, mul_im]
  norm_num

/-- The moving quarter-turn radius has an explicit fibre limit. -/
theorem tendsto_xiSignedAtomicQuarterTurnRadiusAt
    (sigma : ℂ) (hsigmaIm : sigma.im ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ => xiSignedAtomicQuarterTurnRadiusAt
        (xiCTaylorAnisotropicCenteredPoint sigma n))
      Filter.atTop (nhds (xiSignedAtomicLimitRadius sigma)) := by
  have hre : Filter.Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).re)
      Filter.atTop (nhds sigma.im) := by
    have h :=
      Complex.continuous_re.continuousAt.tendsto.comp
        (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
    simpa [Function.comp_def, xiCTaylorCenteredPoint_re] using h
  have him : Filter.Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      Filter.atTop (nhds (1 / 2 - sigma.re)) := by
    have h :=
      Complex.continuous_im.continuousAt.tendsto.comp
        (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
    simpa [Function.comp_def, xiCTaylorCenteredPoint_im] using h
  have hden : 2 * sigma.im ≠ 0 := mul_ne_zero (by norm_num) hsigmaIm
  have hscale : Filter.Tendsto
      (fun n : ℕ => Real.pi /
        (2 * (xiCTaylorAnisotropicCenteredPoint sigma n).re))
      Filter.atTop (nhds (Real.pi / (2 * sigma.im))) := by
    change Filter.Tendsto
      ((fun _ : ℕ => Real.pi) /
        (fun n : ℕ => 2 *
          (xiCTaylorAnisotropicCenteredPoint sigma n).re))
      Filter.atTop (nhds (Real.pi / (2 * sigma.im)))
    exact tendsto_const_nhds.div (tendsto_const_nhds.mul hre) hden
  have harg := (hscale.mul him).neg
  simpa only [xiSignedAtomicQuarterTurnRadiusAt,
    xiSignedAtomicLimitRadius, Function.comp_def] using
    (Real.continuous_exp.tendsto _).comp harg

/-- Equality of positive-ordinate fibre radii is exactly equality of slopes from the critical
centre. -/
theorem xiSignedAtomicLimitRadius_eq_iff_slope_eq
    {sigma tau : ℂ} (hsigmaIm : 0 < sigma.im) (htauIm : 0 < tau.im) :
    xiSignedAtomicLimitRadius sigma = xiSignedAtomicLimitRadius tau ↔
      (1 / 2 - sigma.re) / sigma.im =
        (1 / 2 - tau.re) / tau.im := by
  constructor
  · intro hradius
    have hexp :
        -(Real.pi / (2 * sigma.im) * (1 / 2 - sigma.re)) =
          -(Real.pi / (2 * tau.im) * (1 / 2 - tau.re)) := by
      exact Real.exp_injective hradius
    have hfactor :
        (-Real.pi / 2) * ((1 / 2 - sigma.re) / sigma.im) =
          (-Real.pi / 2) * ((1 / 2 - tau.re) / tau.im) := by
      calc
        (-Real.pi / 2) * ((1 / 2 - sigma.re) / sigma.im) =
            -(Real.pi / (2 * sigma.im) *
              (1 / 2 - sigma.re)) := by
                field_simp [hsigmaIm.ne']
        _ = -(Real.pi / (2 * tau.im) *
              (1 / 2 - tau.re)) := hexp
        _ = (-Real.pi / 2) * ((1 / 2 - tau.re) / tau.im) := by
                field_simp [htauIm.ne']
    have hfactorNe : (-Real.pi / 2 : ℝ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (ne_of_gt Real.pi_pos)) (by norm_num)
    exact mul_left_cancel₀ hfactorNe hfactor
  · intro hslope
    rw [xiSignedAtomicLimitRadius, xiSignedAtomicLimitRadius]
    apply congrArg Real.exp
    calc
      -(Real.pi / (2 * sigma.im) * (1 / 2 - sigma.re)) =
          (-Real.pi / 2) * ((1 / 2 - sigma.re) / sigma.im) := by
            field_simp [hsigmaIm.ne']
      _ = (-Real.pi / 2) * ((1 / 2 - tau.re) / tau.im) := by rw [hslope]
      _ = -(Real.pi / (2 * tau.im) * (1 / 2 - tau.re)) := by
            field_simp [htauIm.ne']

/-- Reflection-invariant projective source directions cannot screen a point off the critical
line.  Representatives may differ by mesh normalization; only their projective cross product
must agree. -/
theorem reflectionProjective_signedEvenQuarterTurn_profile_forces_criticalLine
    {sigma : ℂ} (hsigmaIm : 0 < sigma.im)
    {a₂ a₄ a₂mate a₄mate : ℕ → ℝ}
    {b₂ b₄ c₂ c₄ : ℝ}
    (hb₄ : b₄ ≠ 0) (hc₄ : c₄ ≠ 0)
    (hprojective : b₂ * c₄ = c₂ * b₄)
    (hb₂sigma : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * a₂ n)
      Filter.atTop (nhds b₂))
    (hb₄sigma : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * a₄ n)
      Filter.atTop (nhds b₄))
    (hb₂mate : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n *
        a₂mate n)
      Filter.atTop (nhds c₂))
    (hb₄mate : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n *
        a₄mate n)
      Filter.atTop (nhds c₄))
    (hGsigma : ∀ n : ℕ,
      signedQuarterTurnCompletion
        (xiSignedAtomicQuarterTurnRadiusAt
          (xiCTaylorAnisotropicCenteredPoint sigma n))
        0 (a₂ n) 0 (a₄ n) = 1)
    (hGmate : ∀ n : ℕ,
      signedQuarterTurnCompletion
        (xiSignedAtomicQuarterTurnRadiusAt
          (xiCTaylorAnisotropicCenteredPoint
            (1 - starRingEnd ℂ sigma) n))
        0 (a₂mate n) 0 (a₄mate n) = 1) :
    sigma.re = 1 / 2 := by
  have hmateIm : 0 < (1 - starRingEnd ℂ sigma).im := by
    simpa using hsigmaIm
  have hraySigma :=
    tendsto_signedEvenQuarterTurn_projectiveFingerprint
      (tendsto_xiTaylorAnisotropicHorizontalStep sigma)
      (tendsto_xiSignedAtomicQuarterTurnRadiusAt sigma hsigmaIm.ne')
      hb₂sigma hb₄sigma hGsigma
  have hrayMate :=
    tendsto_signedEvenQuarterTurn_projectiveFingerprint
      (tendsto_xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma))
      (tendsto_xiSignedAtomicQuarterTurnRadiusAt
        (1 - starRingEnd ℂ sigma) hmateIm.ne')
      hb₂mate hb₄mate hGmate
  have hradius :
      xiSignedAtomicLimitRadius sigma =
        xiSignedAtomicLimitRadius (1 - starRingEnd ℂ sigma) :=
    proportional_signedEvenQuarterTurn_projectiveFingerprint_rigid
      (Real.exp_pos _) (Real.exp_pos _) hb₄ hc₄
      hraySigma hrayMate hprojective
  have hslope :=
    (xiSignedAtomicLimitRadius_eq_iff_slope_eq
      hsigmaIm hmateIm).mp hradius
  simp at hslope
  field_simp [hsigmaIm.ne'] at hslope
  linarith

/-- Equal normalized representatives are the most direct special case of projective reflection
rigidity. -/
theorem reflectionInvariant_signedEvenQuarterTurn_profile_forces_criticalLine
    {sigma : ℂ} (hsigmaIm : 0 < sigma.im)
    {a₂ a₄ a₂mate a₄mate : ℕ → ℝ} {b₂ b₄ : ℝ}
    (hb₄ : b₄ ≠ 0)
    (hb₂sigma : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * a₂ n)
      Filter.atTop (nhds b₂))
    (hb₄sigma : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * a₄ n)
      Filter.atTop (nhds b₄))
    (hb₂mate : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n *
        a₂mate n)
      Filter.atTop (nhds b₂))
    (hb₄mate : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n *
        a₄mate n)
      Filter.atTop (nhds b₄))
    (hGsigma : ∀ n : ℕ,
      signedQuarterTurnCompletion
        (xiSignedAtomicQuarterTurnRadiusAt
          (xiCTaylorAnisotropicCenteredPoint sigma n))
        0 (a₂ n) 0 (a₄ n) = 1)
    (hGmate : ∀ n : ℕ,
      signedQuarterTurnCompletion
        (xiSignedAtomicQuarterTurnRadiusAt
          (xiCTaylorAnisotropicCenteredPoint
            (1 - starRingEnd ℂ sigma) n))
        0 (a₂mate n) 0 (a₄mate n) = 1) :
    sigma.re = 1 / 2 := by
  exact reflectionProjective_signedEvenQuarterTurn_profile_forces_criticalLine
    hsigmaIm hb₄ hb₄ (by ring)
    hb₂sigma hb₄sigma hb₂mate hb₄mate hGsigma hGmate

/-- Exact finite-mesh formula behind the nonzero charge ray.  A residue `m` enters the fourth
weight at order `1/δ`; the bounded connection correction contributes only order one. -/
theorem signedEvenQuarterTurnWeightFour_scaledCharge_eq
    {δ T r : ℝ} (hδ : δ ≠ 0) (hT : T ≠ 0) (hr : r ≠ 0)
    (m c : ℝ) :
    δ * signedEvenQuarterTurnWeightFour T r (m / δ + c) =
      δ / (1 + r ^ (2 : ℕ)) ^ (2 : ℕ) -
        (m + δ * c) / (2 * T * r ^ (2 : ℕ) * (1 + r ^ (2 : ℕ))) := by
  have hsum : 1 + r ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r]
  simp only [signedEvenQuarterTurnWeightFour]
  field_simp [hδ, hT, hr, hsum]

/-- The normalized fourth weight of an exact charge screen has a forced, nonzero limit whenever
the residue is nonzero.  Thus `b₄ ≠ 0` in reflection rigidity is not an extra assumption for a
genuine zero charge. -/
theorem tendsto_signedEvenQuarterTurnWeightFour_scaledCharge
    {δ T r c : ℕ → ℝ} {T₀ r₀ c₀ m : ℝ}
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hT : Filter.Tendsto T Filter.atTop (nhds T₀))
    (hr : Filter.Tendsto r Filter.atTop (nhds r₀))
    (hc : Filter.Tendsto c Filter.atTop (nhds c₀))
    (hδne : ∀ n : ℕ, δ n ≠ 0)
    (hTne : ∀ n : ℕ, T n ≠ 0)
    (hrne : ∀ n : ℕ, r n ≠ 0)
    (hT₀ : T₀ ≠ 0) (hr₀ : r₀ ≠ 0) :
    Filter.Tendsto
      (fun n => δ n *
        signedEvenQuarterTurnWeightFour (T n) (r n)
          (m / δ n + c n))
      Filter.atTop
      (nhds (-(m / (2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ)))))) := by
  have hsum : 1 + r₀ ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r₀]
  have hfirst : Filter.Tendsto
      (fun n => δ n / (1 + (r n) ^ (2 : ℕ)) ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (δ / (fun n => (1 + (r n) ^ (2 : ℕ)) ^ (2 : ℕ)))
      Filter.atTop (nhds 0)
    simpa only [zero_div] using
      hδ.div ((tendsto_const_nhds.add (hr.pow 2)).pow 2)
        (pow_ne_zero 2 hsum)
  have hnum : Filter.Tendsto
      (fun n => m + δ n * c n)
      Filter.atTop (nhds m) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (hδ.mul hc)
  have hden : Filter.Tendsto
      (fun n => 2 * T n * (r n) ^ (2 : ℕ) * (1 + (r n) ^ (2 : ℕ)))
      Filter.atTop
      (nhds (2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ)))) :=
    ((tendsto_const_nhds.mul hT).mul (hr.pow 2)).mul
      (tendsto_const_nhds.add (hr.pow 2))
  have hdenNe : 2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ)) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hT₀)
        (pow_ne_zero 2 hr₀))
      hsum
  have hsecond : Filter.Tendsto
      (fun n => (m + δ n * c n) /
        (2 * T n * (r n) ^ (2 : ℕ) * (1 + (r n) ^ (2 : ℕ))))
      Filter.atTop
      (nhds (m / (2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ))))) := by
    change Filter.Tendsto
      ((fun n => m + δ n * c n) /
        (fun n => 2 * T n * (r n) ^ (2 : ℕ) * (1 + (r n) ^ (2 : ℕ))))
      Filter.atTop
      (nhds (m / (2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ)))))
    exact hnum.div hden hdenNe
  have hright : Filter.Tendsto
      (fun n =>
        δ n / (1 + (r n) ^ (2 : ℕ)) ^ (2 : ℕ) -
          (m + δ n * c n) /
            (2 * T n * (r n) ^ (2 : ℕ) * (1 + (r n) ^ (2 : ℕ))))
      Filter.atTop
      (nhds (-(m / (2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ)))))) := by
    simpa only [zero_sub] using hfirst.sub hsecond
  have heq :
      (fun n => δ n *
        signedEvenQuarterTurnWeightFour (T n) (r n)
          (m / δ n + c n)) =
      (fun n =>
        δ n / (1 + (r n) ^ (2 : ℕ)) ^ (2 : ℕ) -
          (m + δ n * c n) /
            (2 * T n * (r n) ^ (2 : ℕ) * (1 + (r n) ^ (2 : ℕ)))) := by
    funext n
    exact signedEvenQuarterTurnWeightFour_scaledCharge_eq
      (hδne n) (hTne n) (hrne n) m (c n)
  rw [heq]
  exact hright

theorem signedEvenQuarterTurnWeightFour_scaledCharge_limit_ne_zero
    {T₀ r₀ m : ℝ} (hT₀ : T₀ ≠ 0) (hr₀ : r₀ ≠ 0) (hm : m ≠ 0) :
    -(m / (2 * T₀ * r₀ ^ (2 : ℕ) * (1 + r₀ ^ (2 : ℕ)))) ≠ 0 := by
  have hsum : 1 + r₀ ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_nonneg r₀]
  apply neg_ne_zero.mpr
  exact div_ne_zero hm
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hT₀)
        (pow_ne_zero 2 hr₀))
      hsum)

end

end RHTower
