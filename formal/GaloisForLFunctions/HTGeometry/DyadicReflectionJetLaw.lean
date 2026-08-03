import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# The all-orders jet of a dyadic reflection combination

For a function `f` and a centre `s`, the dyadic reflection combination

```text
D(c) = f(s - 2c) - f(s + 2c) - 2 f(s - c) + 2 f(s + c)
```

has an exact derivative tower at `c = 0`: only odd orders survive, and there

```text
D^(n)(0) = -2 (2^n - 2) f^(n)(s).
```

The order-one term vanishes because `2^1 - 2 = 0`, so the combination has contact of order three at
the centre, with `D'''(0) = -12 f'''(s)`; every higher odd order is a nonzero multiple of the
corresponding jet of `f`.  The proof is the scaling law for iterated derivatives along an affine
substitution, applied to the antisymmetric pair `f(s - ac) - f(s + ac)`, whose `n`-th derivative at
zero is `((-a)^n - a^n) f^(n)(s)`.
-/

namespace GaloisForLFunctions

/-! ## Affine substitution -/

/-- The jet of an affine substitution scales by the slope. -/
theorem iteratedDeriv_scaledShift {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (s a c : ℝ) :
    iteratedDeriv n (fun x : ℝ => f (s + a * x)) c = a ^ n * iteratedDeriv n f (s + a * c) := by
  have hg : ContDiff ℝ n (fun y : ℝ => f (s + y)) := hf.comp (contDiff_const.add contDiff_id)
  have h2 : (iteratedDeriv n fun x : ℝ => f (s + a * x))
      = fun x : ℝ => a ^ n • iteratedDeriv n (fun y : ℝ => f (s + y)) (a * x) :=
    iteratedDeriv_comp_const_smul hg a
  have h3 : iteratedDeriv n (fun y : ℝ => f (s + y)) = fun t => iteratedDeriv n f (s + t) :=
    iteratedDeriv_comp_const_add n f s
  rw [h2]
  simp only [h3, smul_eq_mul]

/-! ## The antisymmetric pair -/

/-- **The jet of an antisymmetric pair.**  Only the parity-matching orders survive. -/
theorem iteratedDeriv_reflectionPair {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (s a : ℝ) :
    iteratedDeriv n (fun c : ℝ => f (s - a * c) - f (s + a * c)) 0
      = ((-a) ^ n - a ^ n) * iteratedDeriv n f s := by
  have hrw : (fun c : ℝ => f (s - a * c) - f (s + a * c))
      = (fun c : ℝ => f (s + (-a) * c)) - fun c : ℝ => f (s + a * c) := by
    funext c
    have e1 : s - a * c = s + (-a) * c := by ring
    simp only [Pi.sub_apply, e1]
  have hleft : ContDiffAt ℝ n (fun c : ℝ => f (s + (-a) * c)) 0 :=
    (hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffAt
  have hright : ContDiffAt ℝ n (fun c : ℝ => f (s + a * c)) 0 :=
    (hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffAt
  rw [hrw, iteratedDeriv_sub hleft hright, iteratedDeriv_scaledShift hf s (-a) 0,
    iteratedDeriv_scaledShift hf s a 0]
  simp only [mul_zero, add_zero]
  ring

/-! ## The dyadic combination -/

/-- The dyadic reflection combination of `f` at the centre `s`. -/
noncomputable def dyadicReflectionCombination (f : ℝ → ℝ) (s c : ℝ) : ℝ :=
  f (s - 2 * c) - f (s + 2 * c) - 2 * f (s - c) + 2 * f (s + c)

/-- **The all-orders law.**  The `n`-th jet of the dyadic reflection combination at the centre is
`((-2)^n - 2^n - 2(-1)^n + 2)` times the `n`-th jet of `f`. -/
theorem iteratedDeriv_dyadicReflectionCombination {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (s : ℝ) :
    iteratedDeriv n (dyadicReflectionCombination f s) 0
      = ((-2 : ℝ) ^ n - 2 ^ n - 2 * ((-1 : ℝ) ^ n - 1)) * iteratedDeriv n f s := by
  have hrw : dyadicReflectionCombination f s
      = (fun c : ℝ => f (s - 2 * c) - f (s + 2 * c))
        - fun c : ℝ => 2 * (f (s - 1 * c) - f (s + 1 * c)) := by
    funext c
    have e1 : s - 1 * c = s - c := by ring
    have e2 : s + 1 * c = s + c := by ring
    simp only [dyadicReflectionCombination, Pi.sub_apply, e1, e2]
    ring
  have hpair2 : ContDiffAt ℝ n (fun c : ℝ => f (s - 2 * c) - f (s + 2 * c)) 0 := by
    refine ContDiffAt.sub ?_ ?_
    · exact (hf.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).contDiffAt
    · exact (hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffAt
  have hinner : ContDiffAt ℝ n (fun c : ℝ => f (s - 1 * c) - f (s + 1 * c)) 0 := by
    refine ContDiffAt.sub ?_ ?_
    · exact (hf.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).contDiffAt
    · exact (hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffAt
  have hpair1 : ContDiffAt ℝ n (fun c : ℝ => 2 * (f (s - 1 * c) - f (s + 1 * c))) 0 :=
    contDiffAt_const.mul hinner
  rw [hrw, iteratedDeriv_sub hpair2 hpair1, iteratedDeriv_const_mul _ hinner,
    iteratedDeriv_reflectionPair hf s 2, iteratedDeriv_reflectionPair hf s 1]
  simp only [one_pow]
  ring

/-! ## Parity and the first surviving order -/

/-- Even orders vanish. -/
theorem iteratedDeriv_dyadicReflectionCombination_even {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (s : ℝ) (hn : Even n) :
    iteratedDeriv n (dyadicReflectionCombination f s) 0 = 0 := by
  rw [iteratedDeriv_dyadicReflectionCombination hf s]
  have h1 : ((-2 : ℝ)) ^ n = 2 ^ n := by
    rw [hn.neg_pow]
  have h2 : ((-1 : ℝ)) ^ n = 1 := by
    rw [hn.neg_one_pow]
  rw [h1, h2]
  ring

/-- **Odd orders are the exact multiple `-2(2^n - 2)`.** -/
theorem iteratedDeriv_dyadicReflectionCombination_odd {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (s : ℝ) (hn : Odd n) :
    iteratedDeriv n (dyadicReflectionCombination f s) 0
      = -2 * (2 ^ n - 2) * iteratedDeriv n f s := by
  rw [iteratedDeriv_dyadicReflectionCombination hf s]
  have h1 : ((-2 : ℝ)) ^ n = -(2 ^ n) := by
    rw [hn.neg_pow]
  have h2 : ((-1 : ℝ)) ^ n = -1 := by
    rw [hn.neg_one_pow]
  rw [h1, h2]
  ring

/-- The value at the centre vanishes. -/
theorem dyadicReflectionCombination_zero (f : ℝ → ℝ) (s : ℝ) :
    dyadicReflectionCombination f s 0 = 0 := by
  simp only [dyadicReflectionCombination, mul_zero, sub_zero, add_zero]
  ring

/-- The first derivative vanishes: the dyadic weights cancel at order one. -/
theorem iteratedDeriv_one_dyadicReflectionCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (s : ℝ) :
    iteratedDeriv 1 (dyadicReflectionCombination f s) 0 = 0 := by
  rw [iteratedDeriv_dyadicReflectionCombination hf s]
  norm_num

/-- The second derivative vanishes by parity. -/
theorem iteratedDeriv_two_dyadicReflectionCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (s : ℝ) :
    iteratedDeriv 2 (dyadicReflectionCombination f s) 0 = 0 :=
  iteratedDeriv_dyadicReflectionCombination_even hf s (by decide)

/-- **Exact cubic contact.**  The third jet is `-12` times the third jet of `f`. -/
theorem iteratedDeriv_three_dyadicReflectionCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (s : ℝ) :
    iteratedDeriv 3 (dyadicReflectionCombination f s) 0 = -12 * iteratedDeriv 3 f s := by
  rw [iteratedDeriv_dyadicReflectionCombination hf s]
  norm_num

/-- Every odd order beyond the first is a nonzero multiple of the corresponding jet of `f`. -/
theorem dyadicReflectionCombination_coeff_ne_zero {n : ℕ} (hn : Odd n) (hn1 : n ≠ 1) :
    (-2 : ℝ) * (2 ^ n - 2) ≠ 0 := by
  obtain ⟨k, hk⟩ := hn
  have h3 : 3 ≤ n := by omega
  have hpow : (8 : ℝ) ≤ 2 ^ n := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h3
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · norm_num at h'
  · linarith

/-! ## Local form: smoothness only on an open set

The prime-Euler logarithms of interest are smooth only on a half-line, so the jet law is also proved
under `ContDiffOn` on an open set containing the centre.  Iterated derivatives are local, so the
same induction works with the chain rule applied on the open preimage.
-/

/-- Smoothness of a shifted-scaled composition at the origin, from smoothness on an open set. -/
theorem contDiffAt_scaledShift_of_contDiffOn {n : ℕ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {s a : ℝ} (hs : s ∈ U) (hf : ContDiffOn ℝ n f U) :
    ContDiffAt ℝ n (fun x : ℝ => f (s + a * x)) 0 := by
  have hat : ContDiffAt ℝ n f s := hf.contDiffAt (hU.mem_nhds hs)
  have hinner : ContDiffAt ℝ n (fun x : ℝ => s + a * x) 0 := by fun_prop
  have hcomp : ContDiffAt ℝ n (fun x : ℝ => f (s + a * x)) 0 := by
    have : ContDiffAt ℝ n f ((fun x : ℝ => s + a * x) 0) := by simpa using hat
    exact this.comp 0 hinner
  exact hcomp

/-- **The affine scaling law for jets, local form.** -/
theorem iteratedDeriv_scaledShift_of_contDiffOn {n : ℕ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {s a : ℝ} (hs : s ∈ U) (hf : ContDiffOn ℝ n f U) :
    iteratedDeriv n (fun x : ℝ => f (s + a * x)) 0 = a ^ n * iteratedDeriv n f s := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      have hone : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by
        simp
      have hdiff : DifferentiableOn ℝ f U := hf.differentiableOn hone
      have hderivOn : ContDiffOn ℝ n (deriv f) U := by
        refine hf.deriv_of_isOpen hU ?_
        push_cast
        exact le_refl _
      -- the derivative of the composition, on the open preimage of `U`
      have hpre : IsOpen ((fun x : ℝ => s + a * x) ⁻¹' U) :=
        hU.preimage (by fun_prop)
      have hmem0 : (0 : ℝ) ∈ (fun x : ℝ => s + a * x) ⁻¹' U := by
        simpa using hs
      have hloc : deriv (fun x : ℝ => f (s + a * x))
          =ᶠ[nhds 0] fun x : ℝ => a * deriv f (s + a * x) := by
        refine Filter.eventuallyEq_of_mem (hpre.mem_nhds hmem0) ?_
        intro x hx
        have hfx : DifferentiableAt ℝ f (s + a * x) :=
          hdiff.differentiableAt (hU.mem_nhds hx)
        have hinner : HasDerivAt (fun y : ℝ => s + a * y) a x := by
          simpa using (hasDerivAt_id x).const_mul a |>.const_add s
        have hchain : HasDerivAt (fun y : ℝ => f (s + a * y))
            (deriv f (s + a * x) * a) x :=
          (hfx.hasDerivAt).comp x hinner
        rw [hchain.deriv]
        ring
      have hcontAt : ContDiffAt ℝ n (fun x : ℝ => deriv f (s + a * x)) 0 :=
        contDiffAt_scaledShift_of_contDiffOn hU hs hderivOn
      rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq n hloc,
        iteratedDeriv_const_mul a hcontAt, ih hderivOn, iteratedDeriv_succ' (f := f)]
      ring

/-- **The antisymmetric pair law, local form.** -/
theorem iteratedDeriv_reflectionPair_of_contDiffOn {n : ℕ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {s a : ℝ} (hs : s ∈ U) (hf : ContDiffOn ℝ n f U) :
    iteratedDeriv n (fun c : ℝ => f (s - a * c) - f (s + a * c)) 0
      = ((-a) ^ n - a ^ n) * iteratedDeriv n f s := by
  have hrw : (fun c : ℝ => f (s - a * c) - f (s + a * c))
      = (fun c : ℝ => f (s + (-a) * c)) - fun c : ℝ => f (s + a * c) := by
    funext c
    have e1 : s - a * c = s + (-a) * c := by ring
    simp only [Pi.sub_apply, e1]
  rw [hrw, iteratedDeriv_sub (contDiffAt_scaledShift_of_contDiffOn hU hs hf)
      (contDiffAt_scaledShift_of_contDiffOn hU hs hf),
    iteratedDeriv_scaledShift_of_contDiffOn hU hs hf,
    iteratedDeriv_scaledShift_of_contDiffOn hU hs hf]
  ring

/-- **The all-orders dyadic law, local form.** -/
theorem iteratedDeriv_dyadicReflectionCombination_of_contDiffOn {n : ℕ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {s : ℝ} (hs : s ∈ U) (hf : ContDiffOn ℝ n f U) :
    iteratedDeriv n (dyadicReflectionCombination f s) 0
      = ((-2 : ℝ) ^ n - 2 ^ n - 2 * ((-1 : ℝ) ^ n - 1)) * iteratedDeriv n f s := by
  have hrw : dyadicReflectionCombination f s
      = (fun c : ℝ => f (s - 2 * c) - f (s + 2 * c))
        - fun c : ℝ => 2 * (f (s - 1 * c) - f (s + 1 * c)) := by
    funext c
    have e1 : s - 1 * c = s - c := by ring
    have e2 : s + 1 * c = s + c := by ring
    simp only [dyadicReflectionCombination, Pi.sub_apply, e1, e2]
    ring
  have hsub : ∀ b : ℝ, ContDiffAt ℝ n (fun c : ℝ => f (s - b * c) - f (s + b * c)) 0 := by
    intro b
    have hleft : ContDiffAt ℝ n (fun c : ℝ => f (s - b * c)) 0 := by
      have h := contDiffAt_scaledShift_of_contDiffOn hU hs hf (a := -b)
      have hfun : (fun c : ℝ => f (s + (-b) * c)) = fun c : ℝ => f (s - b * c) := by
        funext c
        congr 1
        ring
      rwa [hfun] at h
    exact hleft.sub (contDiffAt_scaledShift_of_contDiffOn hU hs hf)
  rw [hrw, iteratedDeriv_sub (hsub 2) (contDiffAt_const.mul (hsub 1)),
    iteratedDeriv_const_mul _ (hsub 1),
    iteratedDeriv_reflectionPair_of_contDiffOn hU hs hf,
    iteratedDeriv_reflectionPair_of_contDiffOn hU hs hf]
  simp only [one_pow]
  ring

/-- Odd orders, local form. -/
theorem iteratedDeriv_dyadicReflectionCombination_odd_of_contDiffOn {n : ℕ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {s : ℝ} (hs : s ∈ U) (hf : ContDiffOn ℝ n f U) (hn : Odd n) :
    iteratedDeriv n (dyadicReflectionCombination f s) 0
      = -2 * (2 ^ n - 2) * iteratedDeriv n f s := by
  rw [iteratedDeriv_dyadicReflectionCombination_of_contDiffOn hU hs hf, hn.neg_pow, hn.neg_one_pow]
  ring

/-- Even orders, local form. -/
theorem iteratedDeriv_dyadicReflectionCombination_even_of_contDiffOn {n : ℕ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {s : ℝ} (hs : s ∈ U) (hf : ContDiffOn ℝ n f U) (hn : Even n) :
    iteratedDeriv n (dyadicReflectionCombination f s) 0 = 0 := by
  rw [iteratedDeriv_dyadicReflectionCombination_of_contDiffOn hU hs hf, hn.neg_pow, hn.neg_one_pow]
  ring

end GaloisForLFunctions
