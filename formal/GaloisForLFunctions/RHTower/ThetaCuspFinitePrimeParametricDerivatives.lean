import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeParametricResolvent

/-!
# Differential calculus for finite-prime theta factors

The finite Euler factor on the physical even Hilbert carrier is a literal,
ordered product of bounded local factors.  This file proves its exact complex
derivative and its left logarithmic-derivative identity without replacing the
operator product by a scalar model.
-/

noncomputable section

namespace RHTower

/-- Product rule for the physical algebra of continuous endomorphisms. -/
theorem hasDerivAt_evenContinuousLinearMap_mul
    {f g : ℂ → evenSubspace →L[ℂ] evenSubspace}
    {f' g' : evenSubspace →L[ℂ] evenSubspace} {s : ℂ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun z => f z * g z) (f' * g s + f s * g') s := by
  let hcomp : IsBoundedBilinearMap ℂ
      (fun q : (evenSubspace →L[ℂ] evenSubspace) ×
          (evenSubspace →L[ℂ] evenSubspace) => q.1 * q.2) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y z
      ext v
      simp
    · intro x y z
      ext v
      simp
    · intro c x y
      ext v
      simp
    · intro c x y
      ext v
      simp
    · refine ⟨1, by norm_num, ?_⟩
      intro x y
      calc
        ‖x * y‖ ≤ ‖x‖ * ‖y‖ := ContinuousLinearMap.opNorm_comp_le x y
        _ = 1 * ‖x‖ * ‖y‖ := by ring
  have hmul := hcomp.hasFDerivAt (𝕜 := ℂ)
    (E := evenSubspace →L[ℂ] evenSubspace)
    (F := evenSubspace →L[ℂ] evenSubspace)
    (G := evenSubspace →L[ℂ] evenSubspace) (f s, g s)
  have hpair := hf.hasFDerivAt.prodMk (𝕜 := ℂ)
    (E := ℂ) (F := evenSubspace →L[ℂ] evenSubspace)
    (G := evenSubspace →L[ℂ] evenSubspace) hg.hasFDerivAt
  have hresult := hmul.comp (𝕜 := ℂ) (E := ℂ)
    (F := (evenSubspace →L[ℂ] evenSubspace) ×
      (evenSubspace →L[ℂ] evenSubspace))
    (G := evenSubspace →L[ℂ] evenSubspace) s hpair
  have hderiv : HasDerivAt (fun z => f z * g z) (f s * g' + f' * g s) s := by
    simpa [Function.comp_apply, IsBoundedBilinearMap.deriv_apply] using! hresult.hasDerivAt
  simpa [add_comm] using hderiv

/-- The exact derivative of one complex finite-prime factor. -/
def finitePrimeEvenLocalFactorTermAtCDeriv (s : ℂ) (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    evenSubspace →L[ℂ] evenSubspace :=
  ((Real.log (p : ℝ) : ℂ) * Complex.exp (-s * (Real.log (p : ℝ) : ℝ))) •
    ((evenDilationUnitary (p : ℝ) (by
      exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
        evenSubspace →L[ℂ] evenSubspace)

theorem hasDerivAt_finitePrimeEvenLocalFactorTermAtCDeriv
    (s : ℂ) (N : ℕ) (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    HasDerivAt (fun z => finitePrimeEvenLocalFactorTermAtC z N p)
      (finitePrimeEvenLocalFactorTermAtCDeriv s N p) s := by
  simpa only [finitePrimeEvenLocalFactorTermAtCDeriv] using
    hasDerivAt_finitePrimeEvenLocalFactorTermAtC s N p

/-- Product and derivative accumulated together over an ordered prime list. -/
def finitePrimeEvenLocalFactorAtCAux (s : ℂ) (N : ℕ)
    (ps : List {p : ℕ // p ∈ Nat.primesLE N}) :
    (evenSubspace →L[ℂ] evenSubspace) × (evenSubspace →L[ℂ] evenSubspace) :=
  ps.foldr (fun p acc =>
    (finitePrimeEvenLocalFactorTermAtC s N p * acc.1,
      finitePrimeEvenLocalFactorTermAtCDeriv s N p * acc.1 +
        finitePrimeEvenLocalFactorTermAtC s N p * acc.2)) (1, 0)

theorem finitePrimeEvenLocalFactorAtCAux_fst
    (s : ℂ) (N : ℕ) (ps : List {p : ℕ // p ∈ Nat.primesLE N}) :
    (finitePrimeEvenLocalFactorAtCAux s N ps).1 =
      (ps.map (finitePrimeEvenLocalFactorTermAtC s N)).prod := by
  induction ps with
  | nil => simp [finitePrimeEvenLocalFactorAtCAux]
  | cons p ps ih =>
      change finitePrimeEvenLocalFactorTermAtC s N p *
          (finitePrimeEvenLocalFactorAtCAux s N ps).1 =
        finitePrimeEvenLocalFactorTermAtC s N p *
          (ps.map (finitePrimeEvenLocalFactorTermAtC s N)).prod
      rw [ih]

/-- Exact derivative of the ordered finite-prime Euler factor. -/
def finitePrimeEvenLocalFactorAtCDeriv (s : ℂ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  (finitePrimeEvenLocalFactorAtCAux s N (Nat.primesLE N).attach.toList).2

theorem finitePrimeEvenLocalFactorAtC_eq_aux_fst (s : ℂ) (N : ℕ) :
    finitePrimeEvenLocalFactorAtC s N =
      (finitePrimeEvenLocalFactorAtCAux s N (Nat.primesLE N).attach.toList).1 := by
  unfold finitePrimeEvenLocalFactorAtC
  exact (finitePrimeEvenLocalFactorAtCAux_fst s N _).symm

theorem hasDerivAt_finitePrimeEvenLocalFactorAtCAux_fst
    (s : ℂ) (N : ℕ) (ps : List {p : ℕ // p ∈ Nat.primesLE N}) :
    HasDerivAt (fun z => (finitePrimeEvenLocalFactorAtCAux z N ps).1)
      (finitePrimeEvenLocalFactorAtCAux s N ps).2 s := by
  induction ps with
  | nil =>
      simpa [finitePrimeEvenLocalFactorAtCAux] using
        (hasDerivAt_const s (1 : evenSubspace →L[ℂ] evenSubspace))
  | cons p ps ih =>
      simpa [finitePrimeEvenLocalFactorAtCAux] using
        hasDerivAt_evenContinuousLinearMap_mul
          (hasDerivAt_finitePrimeEvenLocalFactorTermAtCDeriv s N p) ih

/-- The finite product is complex differentiable with its literal Leibniz derivative. -/
theorem hasDerivAt_finitePrimeEvenLocalFactorAtC
    (s : ℂ) (N : ℕ) :
    HasDerivAt (fun z => finitePrimeEvenLocalFactorAtC z N)
      (finitePrimeEvenLocalFactorAtCDeriv s N) s := by
  have hfun : (fun z => finitePrimeEvenLocalFactorAtC z N) =
      fun z => (finitePrimeEvenLocalFactorAtCAux z N (Nat.primesLE N).attach.toList).1 := by
    funext z
    exact finitePrimeEvenLocalFactorAtC_eq_aux_fst z N
  rw [hfun]
  simpa only [finitePrimeEvenLocalFactorAtCDeriv] using
    hasDerivAt_finitePrimeEvenLocalFactorAtCAux_fst s N (Nat.primesLE N).attach.toList

/-- The left logarithmic derivative of the finite Euler factor. -/
noncomputable def finitePrimeEvenLocalFactorAtCLogDeriv
    (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  finitePrimeEvenResolventAtC s hs N * finitePrimeEvenLocalFactorAtCDeriv s N

/-- The left logarithmic derivative reconstructs the literal derivative after multiplication by
the invertible finite Euler factor. -/
theorem finitePrimeEvenLocalFactorAtC_mul_logDeriv
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    finitePrimeEvenLocalFactorAtC s N *
        finitePrimeEvenLocalFactorAtCLogDeriv s hs N =
      finitePrimeEvenLocalFactorAtCDeriv s N := by
  rw [finitePrimeEvenLocalFactorAtCLogDeriv, ← mul_assoc,
    finitePrimeEvenLocalFactorAtC_mul_resolvent, one_mul]

end RHTower
