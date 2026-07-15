import GaloisForLFunctions.HTGeometry.PrimePowerTailPacket
import GaloisForLFunctions.HTGeometry.PrimeDirichletAnalyticTransfer
import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# Analytic realization of prime-power layers

The arithmetic carrier supported at `p^(e+1)` is exactly the `(e+1)`-st power dilation of its
prime-supported source.  Hence its Dirichlet series is the original prime Dirichlet series at the
dilated argument `(e+1)s`.  The nonuniform prime-power packet theorem therefore transfers without
loss to actual analytic upper-end germs.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set

noncomputable section

open scoped LSeries.notation

universe u

/-- A prime-power column is the ordinary power dilation of its prime-supported source. -/
theorem mPart_arithmeticOfPrimeColumn
    (e : ℕ) (a : Nat.Primes → ℂ) :
    RHTower.mPart (e + 1) (arithmeticOfPrimeColumn a) =
      arithmeticOfPrimePowerColumn e a := by
  classical
  ext n
  by_cases hroot : ∃ k : ℕ, k ^ (e + 1) = n
  · obtain ⟨k, rfl⟩ := hroot
    rw [RHTower.mPart_apply_pow (Nat.succ_ne_zero e)]
    by_cases hk : k.Prime
    · let p : Nat.Primes := ⟨k, hk⟩
      rw [show arithmeticOfPrimeColumn a k = a p by
        exact arithmeticOfPrimeColumn_apply_prime a p]
      simpa [p] using (arithmeticOfPrimePowerColumn_apply e a p).symm
    · have hnone : ¬ ∃ p : Nat.Primes, k ^ (e + 1) = (p : ℕ) ^ (e + 1) := by
        rintro ⟨p, hp⟩
        have hkp : k = (p : ℕ) := Nat.pow_left_injective (Nat.succ_ne_zero e) hp
        exact hk (hkp.symm ▸ p.2)
      change (if h : k.Prime then a ⟨k, h⟩ else 0) =
        (if h : ∃ p : Nat.Primes, k ^ (e + 1) = (p : ℕ) ^ (e + 1) then
          a (chosenPrimePowerBase (e + 1) (k ^ (e + 1)) h) else 0)
      rw [dif_neg hk, dif_neg hnone]
  · rw [RHTower.mPart_apply_of_forall_pow_ne (e + 1)
      (arithmeticOfPrimeColumn a) (fun k hk => hroot ⟨k, hk⟩)]
    change 0 = (if h : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1) then
      a (chosenPrimePowerBase (e + 1) n h) else 0)
    rw [dif_neg]
    rintro ⟨p, hp⟩
    exact hroot ⟨p, hp.symm⟩

/-- **Analytic prime-power dilation law.**  The L-series of a layer supported at `p^(e+1)` is
the prime-supported source evaluated at `(e+1)s`. -/
theorem LSeries_arithmeticOfPrimePowerColumn
    (e : ℕ) (a : Nat.Primes → ℂ) (s : ℂ) :
    LSeries (fun n => arithmeticOfPrimePowerColumn e a n) s =
      LSeries (fun n => arithmeticOfPrimeColumn a n) (((e + 1 : ℕ) : ℂ) * s) := by
  rw [← mPart_arithmeticOfPrimeColumn e a]
  exact RHTower.LSeries_mPart (Nat.succ_ne_zero e) (arithmeticOfPrimeColumn a) s

/-- Absolute convergence transfers exactly along a prime-power layer. -/
theorem LSeriesSummable_arithmeticOfPrimePowerColumn_iff
    (e : ℕ) (a : Nat.Primes → ℂ) (s : ℂ) :
    LSeriesSummable (fun n => arithmeticOfPrimePowerColumn e a n) s ↔
      LSeriesSummable (fun n => arithmeticOfPrimeColumn a n)
        (((e + 1 : ℕ) : ℂ) * s) := by
  rw [← mPart_arithmeticOfPrimeColumn e a]
  exact RHTower.LSeriesSummable_mPart_iff
    (Nat.succ_ne_zero e) (arithmeticOfPrimeColumn a) s

/-- The power dilation of any finite-abscissa Dirichlet carrier again has finite abscissa. -/
def finiteAbscissaPrimePowerDilation
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨RHTower.mPart (e + 1) f.1, ?_⟩
  obtain ⟨H, hH⟩ := f.2
  refine ⟨max H 0 + 1, fun y hy => ?_⟩
  rw [RHTower.LSeriesSummable_mPart_iff (Nat.succ_ne_zero e)]
  have hyH : H < y := lt_of_le_of_lt (le_max_left H 0) (lt_add_one _ |>.trans hy)
  have hy0 : 0 < y := lt_of_le_of_lt (le_max_right H 0) (lt_add_one _ |>.trans hy)
  have hscale : H < ((e + 1 : ℕ) : ℝ) * y := by
    have hone : (1 : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le e)
    nlinarith
  simpa using hH (((e + 1 : ℕ) : ℝ) * y) hscale

@[simp]
theorem finiteAbscissaPrimePowerDilation_apply
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra) (n : ℕ) :
    (finiteAbscissaPrimePowerDilation e f).1 n = RHTower.mPart (e + 1) f.1 n :=
  rfl

/-- Prime-supported finite-abscissa sources become exactly the new prime-power columns. -/
theorem finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra) (a : Nat.Primes → ℂ)
    (hf : f.1 = arithmeticOfPrimeColumn a) :
    (finiteAbscissaPrimePowerDilation e f).1 = arithmeticOfPrimePowerColumn e a := by
  change RHTower.mPart (e + 1) f.1 = arithmeticOfPrimePowerColumn e a
  rw [hf, mPart_arithmeticOfPrimeColumn]

/-- **Prime-power chain law on coefficients.**  Rotated logarithmic differentiation of an
`(e+1)`-fold dilation is `(e+1)` times the dilation of the rotated derivative. -/
theorem finiteAbscissaRotatedDeriv_primePowerDilation
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaRotatedDeriv (finiteAbscissaPrimePowerDilation e f) =
      (((e + 1 : ℕ) : ℂ) •
        finiteAbscissaPrimePowerDilation e (finiteAbscissaRotatedDeriv f)) := by
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  rw [finiteAbscissaRotatedDeriv_apply]
  simp only [finiteAbscissaPrimePowerDilation_apply]
  change Complex.I * (Real.log n : ℂ) * RHTower.mPart (e + 1) f.1 n =
    (((e + 1 : ℕ) : ℂ) *
      RHTower.mPart (e + 1) (finiteAbscissaRotatedDeriv f).1 n)
  by_cases hroot : ∃ k : ℕ, k ^ (e + 1) = n
  · obtain ⟨k, rfl⟩ := hroot
    rw [RHTower.mPart_apply_pow (Nat.succ_ne_zero e),
      RHTower.mPart_apply_pow (Nat.succ_ne_zero e),
      finiteAbscissaRotatedDeriv_apply]
    have hlog : Real.log ((k ^ (e + 1) : ℕ) : ℝ) =
        ((e + 1 : ℕ) : ℝ) * Real.log (k : ℝ) := by
      rw [show ((k ^ (e + 1) : ℕ) : ℝ) = (k : ℝ) ^ (e + 1) by norm_num,
        Real.log_pow]
    rw [hlog]
    push_cast
    ring
  · rw [RHTower.mPart_apply_of_forall_pow_ne (e + 1) f.1
        (fun k hk => hroot ⟨k, hk⟩),
      RHTower.mPart_apply_of_forall_pow_ne (e + 1)
        (finiteAbscissaRotatedDeriv f).1 (fun k hk => hroot ⟨k, hk⟩)]
    ring

/-- **All-order prime-power chain law on coefficients.**  The `k`-th rotated derivative of an
`(e+1)`-fold dilation is `(e+1)^k` times the dilation of the `k`-th rotated derivative. -/
theorem finiteAbscissaRotatedDeriv_iterate_primePowerDilation
    (e k : ℕ) (f : finiteAbscissaArithmeticSubalgebra) :
    ((finiteAbscissaRotatedDeriv^[k]) (finiteAbscissaPrimePowerDilation e f)) =
      (((((e + 1 : ℕ) : ℂ) ^ k)) •
        finiteAbscissaPrimePowerDilation e ((finiteAbscissaRotatedDeriv^[k]) f)) := by
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  rw [finiteAbscissaRotatedDeriv_iterate_apply]
  simp only [finiteAbscissaPrimePowerDilation_apply]
  change (Complex.I * (Real.log n : ℂ)) ^ k * RHTower.mPart (e + 1) f.1 n =
    (((e + 1 : ℕ) : ℂ) ^ k *
      RHTower.mPart (e + 1) ((finiteAbscissaRotatedDeriv^[k]) f).1 n)
  by_cases hroot : ∃ q : ℕ, q ^ (e + 1) = n
  · obtain ⟨q, rfl⟩ := hroot
    rw [RHTower.mPart_apply_pow (Nat.succ_ne_zero e),
      RHTower.mPart_apply_pow (Nat.succ_ne_zero e),
      finiteAbscissaRotatedDeriv_iterate_apply]
    have hlog : Real.log ((q ^ (e + 1) : ℕ) : ℝ) =
        ((e + 1 : ℕ) : ℝ) * Real.log (q : ℝ) := by
      rw [show ((q ^ (e + 1) : ℕ) : ℝ) = (q : ℝ) ^ (e + 1) by norm_num,
        Real.log_pow]
    rw [hlog]
    push_cast
    rw [show Complex.I * (((e : ℂ) + 1) * Complex.log (q : ℂ)) =
      (((e : ℂ) + 1) * (Complex.I * Complex.log (q : ℂ))) by ring,
      mul_pow]
    ring
  · rw [RHTower.mPart_apply_of_forall_pow_ne (e + 1) f.1
        (fun q hq => hroot ⟨q, hq⟩),
      RHTower.mPart_apply_of_forall_pow_ne (e + 1)
        ((finiteAbscissaRotatedDeriv^[k]) f).1 (fun q hq => hroot ⟨q, hq⟩)]
    ring

/-- Positive integral scaling preserves the complex upper end. -/
theorem tendsto_primePowerScale_upperEndFilter (e : ℕ) :
    Tendsto (fun z : ℂ => (((e + 1 : ℕ) : ℂ) * z)) upperEndFilter upperEndFilter := by
  rw [upperEndFilter_basis.tendsto_iff upperEndFilter_basis]
  intro H hH
  refine ⟨H / ((e + 1 : ℕ) : ℝ), trivial, ?_⟩
  intro z hz
  change H / ((e + 1 : ℕ) : ℝ) < z.im at hz
  change H < ((((e + 1 : ℕ) : ℂ) * z).im)
  have hpos : (0 : ℝ) < ((e + 1 : ℕ) : ℝ) := by positivity
  simpa [Complex.mul_im, mul_comm] using (div_lt_iff₀ hpos).mp hz

/-- Precomposition by the integral dilation `z ↦ (e+1)z` on upper-end germs. -/
noncomputable def upperEndPrimePowerScaleGerm (e : ℕ) :
    Germ upperEndFilter ℂ →+* Germ upperEndFilter ℂ where
  toFun f := f.compTendsto (fun z => (((e + 1 : ℕ) : ℂ) * z))
    (tendsto_primePowerScale_upperEndFilter e)
  map_zero' := by rfl
  map_one' := by rfl
  map_add' f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl
  map_mul' f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl

@[simp]
theorem upperEndPrimePowerScaleGerm_coe (e : ℕ) (f : ℂ → ℂ) :
    upperEndPrimePowerScaleGerm e (f : Germ upperEndFilter ℂ) =
      ((fun z => f (((e + 1 : ℕ) : ℂ) * z)) : Germ upperEndFilter ℂ) := by
  rfl

/-- The faithful analytic realization sends arithmetic power dilation to literal argument
dilation of the source germ. -/
theorem finiteAbscissaLSeriesToUpperEndGerm_primePowerDilation
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaLSeriesToUpperEndGerm (finiteAbscissaPrimePowerDilation e f) =
      upperEndPrimePowerScaleGerm e (finiteAbscissaLSeriesToUpperEndGerm f) := by
  change (↑(fun z : ℂ =>
      LSeries (fun n => RHTower.mPart (e + 1) f.1 n) (-Complex.I * z)) :
        Germ upperEndFilter ℂ) =
    upperEndPrimePowerScaleGerm e
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
        Germ upperEndFilter ℂ)
  rw [upperEndPrimePowerScaleGerm_coe, Germ.coe_eq]
  exact Filter.Eventually.of_forall fun z => by
    change LSeries (RHTower.mPart (e + 1) f.1) (-Complex.I * z) =
      LSeries f.1 (-Complex.I * (((e + 1 : ℕ) : ℂ) * z))
    rw [RHTower.LSeries_mPart (Nat.succ_ne_zero e)]
    congr 1
    ring

/-- **Analytic prime-power chain law.**  On every finite-abscissa Dirichlet germ, differentiating
after the integral argument dilation multiplies the dilated derivative by the dilation degree. -/
theorem upperEndGermDeriv_primePowerScale_LSeries
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra) :
    upperEndGermDeriv
        (upperEndPrimePowerScaleGerm e (finiteAbscissaLSeriesToUpperEndGerm f)) =
      algebraMap ℂ (Germ upperEndFilter ℂ) (((e + 1 : ℕ) : ℂ)) *
        upperEndPrimePowerScaleGerm e
          (upperEndGermDeriv (finiteAbscissaLSeriesToUpperEndGerm f)) := by
  rw [← finiteAbscissaLSeriesToUpperEndGerm_primePowerDilation]
  rw [upperEndGermDeriv_finiteAbscissaLSeries]
  rw [finiteAbscissaRotatedDeriv_primePowerDilation]
  rw [map_smul]
  rw [finiteAbscissaLSeriesToUpperEndGerm_primePowerDilation]
  rw [upperEndGermDeriv_finiteAbscissaLSeries]
  rfl

/-- **All-order analytic prime-power chain law.**  Every finite derivative jet transforms with
the exact homogeneous weight `(e+1)^k` under the integral argument dilation. -/
theorem upperEndGermDeriv_iterate_primePowerScale_LSeries
    (e k : ℕ) (f : finiteAbscissaArithmeticSubalgebra) :
    (upperEndGermDeriv^[k])
        (upperEndPrimePowerScaleGerm e (finiteAbscissaLSeriesToUpperEndGerm f)) =
      algebraMap ℂ (Germ upperEndFilter ℂ) ((((e + 1 : ℕ) : ℂ) ^ k)) *
        upperEndPrimePowerScaleGerm e
          ((upperEndGermDeriv^[k]) (finiteAbscissaLSeriesToUpperEndGerm f)) := by
  rw [← finiteAbscissaLSeriesToUpperEndGerm_primePowerDilation]
  rw [← finiteAbscissaLSeriesToUpperEndGerm_iteratedDeriv]
  rw [finiteAbscissaRotatedDeriv_iterate_primePowerDilation]
  rw [map_smul]
  rw [finiteAbscissaLSeriesToUpperEndGerm_primePowerDilation]
  rw [finiteAbscissaLSeriesToUpperEndGerm_iteratedDeriv]
  rfl

/-- **Analytic nonuniform prime-power tower.**  If each finite layer of prime-supported
finite-abscissa sources has independent coefficient tails, then all of their distinct integral
dilations are jointly algebraically independent as actual analytic upper-end germs. -/
theorem algebraicIndependent_primePowerDilatedUpperEndGerms
    {d : ℕ} (A : Fin d → Type*)
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (f : ∀ r, A r → finiteAbscissaArithmeticSubalgebra)
    (a : ∀ r, A r → Nat.Primes → ℂ)
    (hf : ∀ r i, (f r i).1 = arithmeticOfPrimeColumn (a r i))
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    AlgebraicIndependent ℂ
      (fun i : Σ r, A r ↦
        finiteAbscissaLSeriesToUpperEndGerm
          (finiteAbscissaPrimePowerDilation i.1 (f i.1 i.2))) := by
  let g : (Σ r, A r) → finiteAbscissaArithmeticSubalgebra := fun i ↦
    finiteAbscissaPrimePowerDilation i.1 (f i.1 i.2)
  have hpacket := cofinitePrimePowerPacket_of_layerwise_tailIndependent d A a htail
  have hraw := algebraicIndependent_arithmeticPrimePowerColumns_of_cofinitePacket
    (primePowerSigmaExponent (A := A)) (primePowerSigmaCoefficient a) hpacket
  let incl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    finiteAbscissaArithmeticSubalgebra.val
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  have hg : AlgebraicIndependent ℂ g := by
    apply (AlgHom.algebraicIndependent_iff incl hincl).mp
    convert hraw using 1
    funext i
    exact finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn
      i.1 (f i.1 i.2) (a i.1 i.2) (hf i.1 i.2)
  exact hg.map' finiteAbscissaLSeriesToUpperEndGerm_injective

/-- **Signed shift--jet dilation tower.**  For a nonuniform finite collection of dilation layers,
each carrying its own finite orientation alphabet, shift alphabet, and derivative cutoff, the
entire family of dilated signed prime Dirichlet germs is algebraically independent.  Its number of
coordinates is exactly the dependent sum of the layer sizes. -/
theorem signedPrimeShiftedJet_primePowerDilatedUpperEndGerms_algebraicIndependent
    {d : ℕ}
    (J B : Fin d → Type u)
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)] [∀ r, Nonempty (B r)]
    (epsilon : ∀ r, J r → Nat.Primes → Bool)
    (alpha : ∀ r, B r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun b ↦ (alpha r b).re))
    (htail : ∀ r, PrimeOrientationTailIndependent (epsilon r))
    (m : Fin d → ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Σ r, J r × (B r × Fin (m r + 1)) ↦
        finiteAbscissaLSeriesToUpperEndGerm
          (finiteAbscissaPrimePowerDilation x.1
            (signedPrimeShiftedRotatedJet
              (epsilon x.1 x.2.1) (alpha x.1 x.2.2.1) x.2.2.2))) := by
  let A : Fin d → Type u := fun r ↦ J r × (B r × Fin (m r + 1))
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let f : ∀ r, A r → finiteAbscissaArithmeticSubalgebra := fun r x ↦
    signedPrimeShiftedRotatedJet (epsilon r x.1) (alpha r x.2.1) x.2.2
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r x p ↦
    primeDirichletSign (epsilon r x.1 p) * primeShiftFactor (alpha r x.2.1) p *
      rotatedPrimeLogClock p ^ (x.2.2 : ℕ)
  have hfa : ∀ r x, (f r x).1 = arithmeticOfPrimeColumn (a r x) := by
    intro r x
    exact signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
      (epsilon r x.1) (alpha r x.2.1) x.2.2
  have hatail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    exact signedPrimeShiftedRotatedJet_tailIndependent
      (epsilon r) (alpha r) (hdistinct r) (htail r) (m r)
  exact algebraicIndependent_primePowerDilatedUpperEndGerms A f a hfa hatail

end

end GaloisForLFunctions.HTGeometry
