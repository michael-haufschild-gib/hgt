import GaloisForLFunctions.HTGeometry.PaddedSequenceOfDivisor
import GaloisForLFunctions.HTGeometry.EntireZeroDivisorIndex
import GaloisForLFunctions.HTGeometry.EntireLogarithm

/-!
# The Weierstrass factorization theorem

Every entire function `f : ℂ → ℂ` that does not vanish identically factors as

```text
f z = z ^ m · exp (g z) · ∏' n, E_n (z / a n),
```

with `g` entire, `m` the order of vanishing of `f` at the origin, `E_n` the genus-`n` Weierstrass
elementary factor, and `(a n)` an enumeration with multiplicity of the nonzero zeros of `f`, padded
with zeros — which are inert factors — so that the statement is uniform in whether `f` has finitely
or infinitely many zeros.  No growth, order, or summability hypothesis is used.

The proof assembles four corpus layers.  The zero divisor of `f` is indexed with multiplicity by
`ZeroCopy f`; discarding the copies over the origin gives a locally finite family avoiding `0`,
which `exists_paddedZeroSeq` converts into a padded sequence with the same fibres.  The padded
canonical product of increasing genus is entire and has exactly that divisor away from the origin,
so `z ^ m` times it has the divisor of `f` everywhere; equal divisors force an entire nonvanishing
quotient, and a nonvanishing entire function is an exponential.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

variable {f : ℂ → ℂ}

/-! ### Finiteness of the order -/

/-- An entire function that is somewhere nonzero vanishes to finite order at every point: an
infinite order means local vanishing, and `ℂ` is connected. -/
theorem analyticOrderAt_ne_top_of_entire (hf : Differentiable ℂ f) {z₁ : ℂ} (hz₁ : f z₁ ≠ 0)
    (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro h
  have hAn : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
  have hev : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp h] with w hw
    simpa using hw
  have hzero := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hev
  exact hz₁ (by simpa using hzero (Set.mem_univ z₁))

/-! ### The zero divisor away from the origin -/

/-- The multiplicity copies of the zero divisor of `f` that sit away from the origin. -/
abbrev NonzeroZeroCopy (f : ℂ → ℂ) : Type := {q : ZeroCopy f // zeroCopyPoint f q ≠ 0}

/-- The divisor point attached to a multiplicity copy away from the origin. -/
def nonzeroZeroCopyPoint (f : ℂ → ℂ) : NonzeroZeroCopy f → ℂ := fun q => zeroCopyPoint f q.1

theorem nonzeroZeroCopyPoint_ne_zero (q : NonzeroZeroCopy f) : nonzeroZeroCopyPoint f q ≠ 0 := q.2

theorem locallyFinite_nonzeroZeroCopyPoint (hf : AnalyticOnNhd ℂ f univ) (r : ℝ) :
    {q : NonzeroZeroCopy f | ‖nonzeroZeroCopyPoint f q‖ ≤ r}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine (locallyFinite_zeroCopyPoint hf r).subset ?_
  rintro _ ⟨q, hq, rfl⟩
  exact hq

/-- Away from the origin the two indexings of the zero divisor have the same fibres. -/
theorem ncard_nonzeroZeroCopy_fiber {w : ℂ} (hw : w ≠ 0) :
    {q : NonzeroZeroCopy f | nonzeroZeroCopyPoint f q = w}.ncard
      = {p : ZeroCopy f | zeroCopyPoint f p = w}.ncard := by
  have himg : Subtype.val '' {q : NonzeroZeroCopy f | nonzeroZeroCopyPoint f q = w}
      = {p : ZeroCopy f | zeroCopyPoint f p = w} := by
    ext p
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p, by rw [hp]; exact hw⟩, hp, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

/-! ### The product in explicit form -/

theorem weierstrassGenusProduct_eq_tprod (a : ℕ → ℂ) (z : ℂ) :
    weierstrassGenusProduct a z = ∏' n : ℕ, weierstrassFactor n (z / a n) := rfl

/-! ### The theorem -/

/-- **The Weierstrass factorization theorem.**  Every entire function that does not vanish
identically is `z ^ m` times the exponential of an entire function times the canonical product of
increasing genus over an enumeration with multiplicity of its nonzero zeros.  The enumeration is
padded with zeros, which contribute the factor `1`, so the statement covers a finite zero set as
well as an infinite one; `m` is the order of vanishing at the origin. -/
theorem exists_weierstrass_factorization (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) :
    ∃ (m : ℕ) (a : ℕ → ℂ) (g : ℂ → ℂ),
      Differentiable ℂ g ∧
      analyticOrderAt f 0 = (m : ℕ∞) ∧
      PaddedZeroSeq a ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      (∀ w : ℂ, w ≠ 0 → ({n : ℕ | a n = w}.ncard : ℕ∞) = analyticOrderAt f w) ∧
      (∀ z : ℂ, f z = z ^ m * Complex.exp (g z) * ∏' n : ℕ, weierstrassFactor n (z / a n)) := by
  classical
  obtain ⟨z₁, hz₁⟩ := hf0
  have hAn : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
  have hford : ∀ z, analyticOrderAt f z ≠ ⊤ := analyticOrderAt_ne_top_of_entire hf hz₁
  set m : ℕ := (analyticOrderAt f 0).toNat with hmdef
  have hm0 : analyticOrderAt f 0 = (m : ℕ∞) := (ENat.coe_toNat (hford 0)).symm
  obtain ⟨a, hapad, hamem, hafib⟩ :=
    exists_paddedZeroSeq (nonzeroZeroCopyPoint f) (locallyFinite_nonzeroZeroCopyPoint hAn)
  -- the sequence carries exactly the divisor of `f` away from the origin
  have hordfib : ∀ w : ℂ, w ≠ 0 → ({n : ℕ | a n = w}.ncard : ℕ∞) = analyticOrderAt f w := by
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt f w = (k : ℕ∞) :=
      ⟨(analyticOrderAt f w).toNat, (ENat.coe_toNat (hford w)).symm⟩
    rw [hafib w hw, ncard_nonzeroZeroCopy_fiber hw, ncard_zeroCopy_fiber w,
      divisor_univ_eq_analyticOrder hAn w, hk]
    simp
  -- every nonzero entry of the sequence is a zero of `f`
  have hfa : ∀ n, a n ≠ 0 → f (a n) = 0 := by
    intro n hn
    by_contra hne
    have h0 : analyticOrderAt f (a n) = 0 :=
      (hAn (a n) (mem_univ _)).analyticOrderAt_eq_zero.mpr hne
    have hcard := hordfib (a n) hn
    rw [h0] at hcard
    have hpos : 0 < {n' : ℕ | a n' = a n}.ncard :=
      (Set.ncard_pos (finite_zeroIndices_padded hapad hn)).mpr ⟨n, rfl⟩
    have : {n' : ℕ | a n' = a n}.ncard = 0 := by exact_mod_cast hcard
    omega
  -- the model function with the same divisor as `f`
  set P : ℂ → ℂ := (fun z : ℂ => z ^ m) * weierstrassGenusProduct a with hPdef
  have hWdiff : Differentiable ℂ (weierstrassGenusProduct a) :=
    differentiable_weierstrassGenusProduct_padded hapad
  have hPdiff : Differentiable ℂ P := (differentiable_pow m).mul hWdiff
  have hPAn : AnalyticOnNhd ℂ P univ := fun z _ => hPdiff.analyticAt z
  have hPord : ∀ z, analyticOrderAt f z = analyticOrderAt P z := by
    intro z
    have hmono : AnalyticAt ℂ (fun w : ℂ => w ^ m) z := (differentiable_pow m).analyticAt z
    have hW : AnalyticAt ℂ (weierstrassGenusProduct a) z := hWdiff.analyticAt z
    rw [hPdef, analyticOrderAt_mul hmono hW]
    rcases eq_or_ne z 0 with rfl | hz
    · rw [EntireQuotient.analyticOrderAt_monomial m,
        analyticOrderAt_weierstrassGenusProduct_padded_zero hapad, add_zero, hm0]
    · rw [EntireQuotient.analyticOrderAt_monomial_of_ne_zero hz,
        analyticOrderAt_weierstrassGenusProduct_padded hapad hz, zero_add, ← hordfib z hz]
  have hPz₁ : P z₁ ≠ 0 := by
    have h0 : analyticOrderAt P z₁ = 0 := by
      rw [← hPord z₁]
      exact (hAn z₁ (mem_univ _)).analyticOrderAt_eq_zero.mpr hz₁
    exact (hPAn z₁ (mem_univ _)).analyticOrderAt_eq_zero.mp h0
  obtain ⟨h, hhdiff, hhne, hfac⟩ :=
    EntireQuotient.exists_entire_nonvanishing_quotient hAn hPAn hford hPord hPz₁
  obtain ⟨g, hgdiff, _, hg⟩ := HTGeometry.exists_entire_log_of_ne_zero hhdiff hhne
  refine ⟨m, a, fun z => Complex.log (h 0) + g z, hgdiff.const_add _, hm0, hapad, hfa, hordfib,
    fun z => ?_⟩
  rw [hfac z, hg z, hPdef]
  simp only [Pi.mul_apply]
  rw [← weierstrassGenusProduct_eq_tprod a z, Complex.exp_add, Complex.exp_log (hhne 0)]
  ring

/-- **Weierstrass factorization, packaged for a function with no zero at the origin.** -/
theorem exists_weierstrass_factorization_of_ne_zero_at_origin (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) :
    ∃ (a : ℕ → ℂ) (g : ℂ → ℂ),
      Differentiable ℂ g ∧
      PaddedZeroSeq a ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      (∀ w : ℂ, w ≠ 0 → ({n : ℕ | a n = w}.ncard : ℕ∞) = analyticOrderAt f w) ∧
      (∀ z : ℂ, f z = Complex.exp (g z) * ∏' n : ℕ, weierstrassFactor n (z / a n)) := by
  obtain ⟨m, a, g, hgdiff, hm0, hapad, hfa, hordfib, hfac⟩ :=
    exists_weierstrass_factorization hf ⟨0, hf0⟩
  have hm : m = 0 := by
    have h0 : analyticOrderAt f 0 = 0 :=
      (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0
    rw [h0] at hm0
    exact_mod_cast hm0.symm
  subst hm
  refine ⟨a, g, hgdiff, hapad, hfa, hordfib, fun z => ?_⟩
  rw [hfac z]
  ring

end

end GaloisForLFunctions
