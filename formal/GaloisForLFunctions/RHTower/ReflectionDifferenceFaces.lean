import GaloisForLFunctions.RHTower.SignedReflectionParity

/-!
# Reflection parity of finite-difference faces

Forward differences do not preserve the centre of a reflection. A difference in direction `τ`
moves the centre by `-τ/2` and reverses the reflection sign. Iterating over a finite direction
list therefore gives a face function reflected about the centre shifted by half the total
direction, with sign `(-1)^n`.

The all-order consequence is a face-jet selection law: for a symmetric entire function, the
`m`-th derivative of an `n`-fold difference vanishes at the shifted centre whenever `m+n` is odd.
Thus every finite-difference face carries a canonical parity grading fixed by the original
reflection constraint.
-/

namespace RHTower

open Complex

/-- Forward difference in the additive direction `τ`. -/
def forwardDifference (τ : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => f (z + τ) - f z

/-- Iterated forward difference along a finite ordered list of directions. -/
def iteratedForwardDifference : List ℂ → (ℂ → ℂ) → ℂ → ℂ
  | [], f => f
  | τ :: τs, f => forwardDifference τ (iteratedForwardDifference τs f)

/-- One difference shifts a signed-reflection centre by `-τ/2` and flips its sign. -/
theorem forwardDifference_signed_reflection {f : ℂ → ℂ} {c ε τ : ℂ}
    (hsym : ∀ z, f (2 * c - z) = ε * f z) :
    ∀ z, forwardDifference τ f (2 * (c - τ / 2) - z) =
      (-ε) * forwardDifference τ f z := by
  intro z
  rw [forwardDifference, forwardDifference]
  have h1 := hsym z
  have h2 := hsym (z + τ)
  rw [show 2 * (c - τ / 2) - z + τ = 2 * c - z by ring,
    show 2 * (c - τ / 2) - z = 2 * c - (z + τ) by ring,
    h1, h2]
  ring

/-- **Finite-difference reflection law.** An `n`-fold difference of an `ε`-reflected function is
`(-1)^n ε`-reflected about the centre shifted by minus half the sum of the directions. -/
theorem iteratedForwardDifference_signed_reflection {f : ℂ → ℂ} {c ε : ℂ}
    (hsym : ∀ z, f (2 * c - z) = ε * f z) :
    ∀ (τs : List ℂ) z,
      iteratedForwardDifference τs f (2 * (c - τs.sum / 2) - z) =
        (-1 : ℂ) ^ τs.length * ε * iteratedForwardDifference τs f z := by
  intro τs
  induction τs with
  | nil =>
      intro z
      simpa [iteratedForwardDifference] using hsym z
  | cons τ τs ih =>
      intro z
      have hstep := forwardDifference_signed_reflection (τ := τ)
        (c := c - τs.sum / 2) (ε := (-1 : ℂ) ^ τs.length * ε) ih z
      simp only [iteratedForwardDifference, List.sum_cons, List.length_cons]
      convert hstep using 1 <;> ring_nf

/-- Symmetric specialization of the finite-difference reflection law. -/
theorem iteratedForwardDifference_reflection {f : ℂ → ℂ} {c : ℂ}
    (hsym : ∀ z, f (2 * c - z) = f z) (τs : List ℂ) (z : ℂ) :
    iteratedForwardDifference τs f (2 * (c - τs.sum / 2) - z) =
      (-1 : ℂ) ^ τs.length * iteratedForwardDifference τs f z := by
  simpa using iteratedForwardDifference_signed_reflection (ε := (1 : ℂ))
    (fun z => by simpa using hsym z) τs z

/-- A forward difference of an entire function is entire. -/
theorem forwardDifference_analyticOnNhd_univ {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (τ : ℂ) :
    AnalyticOnNhd ℂ (forwardDifference τ f) Set.univ := by
  intro z hz
  have haffine : AnalyticAt ℂ (fun w : ℂ => w + τ) z :=
    analyticAt_id.add analyticAt_const
  have hcomp := (hf (z + τ) (Set.mem_univ _)).comp (f := fun w : ℂ => w + τ) haffine
  have hshift : AnalyticAt ℂ (fun w : ℂ => f (w + τ)) z := by
    simpa [Function.comp_def] using hcomp
  exact hshift.sub (hf z hz)

/-- Every finite iterated forward difference of an entire function is entire. -/
theorem iteratedForwardDifference_analyticOnNhd_univ {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    ∀ τs : List ℂ, AnalyticOnNhd ℂ (iteratedForwardDifference τs f) Set.univ
  | [] => by simpa [iteratedForwardDifference] using hf
  | τ :: τs => by
      simpa [iteratedForwardDifference] using
        forwardDifference_analyticOnNhd_univ
          (iteratedForwardDifference_analyticOnNhd_univ hf τs) τ

/-- **All-order face-jet parity.** For a symmetric entire function, the `m`-th derivative of an
`n`-fold difference vanishes at the shifted reflection centre whenever `m+n` is odd. Thus the
complete face jet is supported in the parity determined by the face codimension. -/
theorem iteratedDeriv_iteratedForwardDifference_center_eq_zero_of_odd
    {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hsym : ∀ z, f (2 * c - z) = f z) (τs : List ℂ) (m : ℕ)
    (hodd : Odd (m + τs.length)) :
    (deriv^[m] (iteratedForwardDifference τs f)) (c - τs.sum / 2) = 0 := by
  let cFace : ℂ := c - τs.sum / 2
  let face : ℂ → ℂ := iteratedForwardDifference τs f
  have hface : AnalyticOnNhd ℂ face Set.univ :=
    iteratedForwardDifference_analyticOnNhd_univ hf τs
  have hfaceSym : ∀ z, face (2 * cFace - z) = (-1 : ℂ) ^ τs.length * face z := by
    intro z
    exact iteratedForwardDifference_reflection hsym τs z
  have h := iteratedDeriv_signed_reflection hface hfaceSym m cFace
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ τs.length = -1 := by
    rw [← pow_add, hodd.neg_one_pow]
  rw [show 2 * cFace - cFace = cFace by ring, hsign] at h
  linear_combination (1 / 2 : ℂ) * h

/-- At even face codimension, the shifted reflection centre has even vanishing order. -/
theorem analyticOrderAt_iteratedForwardDifference_even_of_symmetric
    {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hsym : ∀ z, f (2 * c - z) = f z) (τs : List ℂ) (hlen : Even τs.length)
    (hne : analyticOrderAt (iteratedForwardDifference τs f) (c - τs.sum / 2) ≠ ⊤) :
    Even (analyticOrderAt (iteratedForwardDifference τs f)
      (c - τs.sum / 2)).toNat := by
  apply analyticOrderAt_even_of_reflection
    (iteratedForwardDifference_analyticOnNhd_univ hf τs) _ hne
  intro z
  have h := iteratedForwardDifference_reflection hsym τs z
  rw [hlen.neg_one_pow, one_mul] at h
  exact h

/-- At odd face codimension, the shifted reflection centre has odd vanishing order. -/
theorem analyticOrderAt_iteratedForwardDifference_odd_of_symmetric
    {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hsym : ∀ z, f (2 * c - z) = f z) (τs : List ℂ) (hlen : Odd τs.length)
    (hne : analyticOrderAt (iteratedForwardDifference τs f) (c - τs.sum / 2) ≠ ⊤) :
    Odd (analyticOrderAt (iteratedForwardDifference τs f)
      (c - τs.sum / 2)).toNat := by
  apply analyticOrderAt_odd_of_antireflection
    (iteratedForwardDifference_analyticOnNhd_univ hf τs) _ hne
  intro z
  have h := iteratedForwardDifference_reflection hsym τs z
  rw [hlen.neg_one_pow] at h
  simpa using h

end RHTower
