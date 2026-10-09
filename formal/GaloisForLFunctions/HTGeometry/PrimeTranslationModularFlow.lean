import GaloisForLFunctions.HTGeometry.DiscreteCrossedProductCStar
import GaloisForLFunctions.HTGeometry.ApertureLogTranslation

/-!
# The prime-graded modular flow on the prime-translation crossed product

The prime-marked translations `Γ = ⊕_p ℤ` act on the logarithmic aperture line through the
length `ℓ(γ) = ∑_p γ_p log p`, hence on `C₀(ℝ)` by `f ↦ f(· + ℓ(γ))`.

* **(SAC.17)** For every real grade `a`, `β^a_t(f U_γ) = exp(i t a ℓ(γ)) f U_γ` is a one-parameter
  group of `*`-automorphisms of the algebraic crossed product `C₀(ℝ) ⋊_alg Γ`: the character law
  for `ℓ` gives multiplicativity and the unimodular values give `*`-preservation.  It extends to the
  full crossed product as a strongly continuous one-parameter group of isometric
  `*`-automorphisms.
* The functional-equation reflection `f ↦ f(-·)`, `γ ↦ -γ` conjugates `β^a` to `β^{-a}`.
* The imaginary-time value `t = -i` is the nonunitary Euler scaling by
  `exp(a ℓ(γ)) = ∏_p p^{a γ_p}`, of modulus `≠ 1` for every nonzero grade.

Hence the existence of prime-marked crossed-product dynamics is unconditional in the grade: it
holds for every real `a` and selects none.
-/

set_option autoImplicit false

open scoped ZeroAtInfty

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Prime-power translations of the logarithmic aperture line -/

/-- The prime-marked translation group `Γ = ⊕_p ℤ`. -/
abbrev PrimeTranslations : Type := Nat.Primes →₀ ℤ

/-- The logarithmic length `ℓ(γ) = ∑_p γ_p log p` of a prime-marked translation. -/
def primeLength : PrimeTranslations →+ ℝ :=
  Finsupp.liftAddHom fun p => zmultiplesHom ℝ (Real.log (p : ℕ))

theorem primeLength_single (p : Nat.Primes) (k : ℤ) :
    primeLength (Finsupp.single p k) = k * Real.log (p : ℕ) := by
  simp [primeLength, zsmul_eq_mul]

theorem primeLength_apply (γ : PrimeTranslations) :
    primeLength γ = γ.sum fun p k => (k : ℝ) * Real.log (p : ℕ) := by
  rw [primeLength, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun p _ => ?_
  simp [zsmul_eq_mul]

/-- Translation by `h` of `C₀(ℝ)` as a `*`-automorphism, `f ↦ f(· + h)`. -/
def translateAut (h : ℝ) : C₀(ℝ, ℂ) ≃⋆ₐ[ℂ] C₀(ℝ, ℂ) where
  toFun := translateC0 h
  invFun := translateC0 (-h)
  left_inv f := by ext x; simp [translateC0_apply]
  right_inv f := by ext x; simp [translateC0_apply]
  map_add' f g := by ext x; simp [translateC0_apply]
  map_mul' f g := by ext x; simp [translateC0_apply]
  map_smul' c f := by ext x; simp [translateC0_apply]
  map_star' f := by ext x; simp [translateC0_apply]

theorem translateAut_apply (h : ℝ) (f : C₀(ℝ, ℂ)) (x : ℝ) : translateAut h f x = f (x + h) := rfl

/-- The prime-translation action `γ ↦ (f ↦ f(· + ℓ(γ)))` on `C₀(ℝ)`. -/
def primeTranslationAction : Multiplicative PrimeTranslations →* (C₀(ℝ, ℂ) ≃⋆ₐ[ℂ] C₀(ℝ, ℂ)) where
  toFun γ := translateAut (primeLength (Multiplicative.toAdd γ))
  map_one' := by
    ext f x
    simp [translateAut_apply]
  map_mul' γ δ := by
    ext f x
    simp only [toAdd_mul, map_add, StarAlgEquiv.aut_mul, StarAlgEquiv.trans_apply,
      translateAut_apply]
    ring_nf

/-- **The algebraic prime-translation crossed product** `C₀(ℝ) ⋊_alg ⊕_p ℤ`. -/
abbrev PrimeCrossed : Type := AlgCrossed primeTranslationAction

/-- **The full prime-translation crossed product.** -/
abbrev FullPrimeCrossed : Type 1 := FullCrossed primeTranslationAction

theorem crossedAct_prime (γ : PrimeTranslations) (f : C₀(ℝ, ℂ)) (x : ℝ) :
    crossedAct primeTranslationAction γ f x = f (x + primeLength γ) := rfl

/-! ## (SAC.17) The prime-graded modular flow -/

/-- **(SAC.17)** For every real grade `a`, the unitary one-parameter group
`β^a_t(f U_γ) = exp(i t a ℓ(γ)) f U_γ` of `*`-automorphisms of the algebraic prime-translation
crossed product. -/
def primeModularFlow (a t : ℝ) : PrimeCrossed ≃⋆ₐ[ℂ] PrimeCrossed :=
  modularFlow primeTranslationAction primeLength a t

theorem primeModularFlow_single (a t : ℝ) (γ : PrimeTranslations) (f : C₀(ℝ, ℂ)) :
    primeModularFlow a t (AlgCrossed.single _ γ f) =
      AlgCrossed.single _ γ (Complex.exp (↑(t * a * primeLength γ) * Complex.I) • f) :=
  modularFlow_single _ _ a t γ f

theorem primeModularFlow_add (a s t : ℝ) (x : PrimeCrossed) :
    primeModularFlow a (s + t) x = primeModularFlow a s (primeModularFlow a t x) :=
  modularFlow_add _ _ a s t x

/-- The character values are unimodular: `|exp(i t a ℓ(γ))| = 1`. -/
theorem norm_primeFlowCharacter (a t : ℝ) (γ : PrimeTranslations) :
    ‖Complex.exp (↑(t * a * primeLength γ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- **The flow extends to the full crossed product** as a strongly continuous one-parameter group
of isometric `*`-automorphisms. -/
theorem fullPrimeModularFlow_spec (a : ℝ) :
    (∀ x : PrimeCrossed, ∀ t, fullModularFlow _ primeLength a t (toFullCrossed _ x) =
      toFullCrossed _ (primeModularFlow a t x)) ∧
    (∀ s t (y : FullPrimeCrossed), fullModularFlow _ primeLength a (s + t) y =
      fullModularFlow _ primeLength a s (fullModularFlow _ primeLength a t y)) ∧
    (∀ y : FullPrimeCrossed, fullModularFlow _ primeLength a 0 y = y) ∧
    (∀ t (y : FullPrimeCrossed), ‖fullModularFlow _ primeLength a t y‖ = ‖y‖) ∧
    (∀ y : FullPrimeCrossed, Continuous fun t => fullModularFlow _ primeLength a t y) :=
  ⟨fun x t => fullModularFlow_toFullCrossed _ _ a t x, fullModularFlow_add _ _ a,
    fullModularFlow_zero _ _ a, fun _ y => norm_starAlgEquiv_apply _ y,
    continuous_fullModularFlow_apply _ _ a⟩

/-! ## Functional-equation reflection sends `a` to `-a` -/

/-- The reflection `f ↦ f(-·)` of `C₀(ℝ)`. -/
def reflectC0 : C₀(ℝ, ℂ) ≃⋆ₐ[ℂ] C₀(ℝ, ℂ) where
  toFun f := f.comp (Homeomorph.neg ℝ).toCocompactMap
  invFun f := f.comp (Homeomorph.neg ℝ).toCocompactMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; simp
  map_mul' f g := by ext x; simp
  map_smul' c f := by ext x; simp
  map_star' f := by ext x; simp

theorem reflectC0_apply (f : C₀(ℝ, ℂ)) (x : ℝ) : reflectC0 f x = f (-x) := rfl

theorem reflectC0_reversing : IsActionReversing primeTranslationAction reflectC0 := by
  intro γ f
  ext x
  rw [reflectC0_apply, crossedAct_prime, crossedAct_prime, reflectC0_apply]
  congr 1
  rw [map_neg]
  ring

/-- **The functional-equation reflection conjugates the prime modular flow of grade `a` to grade
`-a`**, on the algebraic and on the full crossed product. -/
theorem primeReflection_conjugates (a t : ℝ) :
    (∀ x : PrimeCrossed, reflectAut reflectC0_reversing (primeModularFlow a t x) =
      primeModularFlow (-a) t (reflectAut reflectC0_reversing x)) ∧
    (∀ y : FullPrimeCrossed,
      fullCrossedAut _ (reflectAut reflectC0_reversing) (fullModularFlow _ primeLength a t y) =
        fullModularFlow _ primeLength (-a) t
          (fullCrossedAut _ (reflectAut reflectC0_reversing) y)) :=
  ⟨reflectAut_modularFlow reflectC0_reversing primeLength a t,
    fullReflect_fullModularFlow reflectC0_reversing primeLength a t⟩

/-! ## The Euler factor is the imaginary-time value -/

/-- `exp(a ℓ(γ)) = ∏_p p^{a γ_p}`: the Euler weight of a prime-marked translation. -/
theorem exp_primeLength_eq_prod (a : ℝ) (γ : PrimeTranslations) :
    Real.exp (a * primeLength γ) = γ.prod fun p k => ((p : ℕ) : ℝ) ^ (a * k) := by
  rw [primeLength_apply, Finsupp.sum, Finset.mul_sum, Real.exp_sum, Finsupp.prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]
  ring_nf

/-- **The imaginary-time value of the prime modular flow is the Euler scaling**
`f U_γ ↦ (∏_p p^{a γ_p}) f U_γ`. -/
theorem primeComplexTime_neg_I (a : ℝ) (γ : PrimeTranslations) :
    complexTimeChar primeLength a (-Complex.I) γ =
      ((γ.prod fun p k => ((p : ℕ) : ℝ) ^ (a * k) : ℝ) : ℂ) := by
  rw [complexTimeChar_neg_I, exp_primeLength_eq_prod]

/-- At real time the complex-time scaling is the unitary flow. -/
theorem primeComplexTime_real (a t : ℝ) (x : PrimeCrossed) :
    charScale _ (complexTimeChar primeLength a t) x = primeModularFlow a t x := by
  rw [complexTimeChar_real]
  rfl

/-- The Euler scaling is **nonunitary** for every nonzero grade: at `γ = U_2` its value
`2^a` has modulus different from one. -/
theorem primeEulerScaling_not_unitary {a : ℝ} (ha : a ≠ 0) :
    ‖complexTimeChar primeLength a (-Complex.I) (Finsupp.single ⟨2, Nat.prime_two⟩ 1)‖ ≠ 1 := by
  rw [complexTimeChar_neg_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), primeLength_single]
  intro h
  have h2 : a * (((1 : ℤ) : ℝ) * Real.log 2) = 0 := by
    have := Real.exp_eq_one_iff (a * (((1 : ℤ) : ℝ) * Real.log ((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ)))
    push_cast at this ⊢
    exact this.mp (by exact_mod_cast h)
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp only [Int.cast_one, one_mul, mul_eq_zero] at h2
  exact h2.elim ha hlog

end GaloisForLFunctions.HTGeometry
