import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.SexticCharacterProjection
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheAverageRowIsBlindToTheTarget
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CanonicalCharactersAndLossParameters
import GaloisForLFunctions.FamilyContinuationTheory.ThePrincipalRowIsAnEulerProduct

/-!
# Sextic projection of the Poisson target

For the normalized residue average `Eχ`, character orthogonality gives
`Eχ[P] = Y^5 / (1 - Y^6) - η X / (1 - R)` for the complete local row `P`.
Subtracting the explicit geometric term recovers `1 - η X`; the known
residue phase then recovers the reciprocal factor of any specified row.
The identity is matched to the literal local Poisson coefficient series.

On `Re x ≥ 51/100`, `Re z ≥ 17/50`, the completion parameter satisfies
`‖R‖ ≤ Q^(-11/10)`. Normalized residue projection is a contraction, and
restoration has uniformly bounded cost over finite prime sets. The infinite
completion product over good primes has a convergent inverse.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open ArithmeticHarmonicAnalysis.SexticCharacterProjection
open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
variable {F : Type*} [Field F] [Fintype F]

/-- The inverse sextic mode of the complete row over a residue field. -/
def sexticRowTargetMode (χ : MulChar F ℂ) (Q R η X Y V : ℂ) : ℂ :=
  projection χ (fun a => rowLocalSum Q R η X Y V (χ a))

/-- The reciprocal target survives with its full complex phase. -/
theorem sexticRowTargetMode_eq (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (Q R η X Y V : ℂ) (hY : 1-Y^6 ≠ 0) :
    sexticRowTargetMode χ Q R η X Y V =
      Y^5*(1-Y^6)⁻¹ - (1-R)⁻¹*η*X := by
  have he : (fun a : F => rowLocalSum Q R η X Y V (χ a)) =
      (fun _ => (1-V)⁻¹ + (1-R)⁻¹ *
        (R*(1-Q⁻¹)*(1-V)⁻¹ - η*(Q-1)*X*Y*V*(1-V)⁻¹)) +
      (fun a => χ a*Y*(1-χ a*Y)⁻¹) +
      ((1-R)⁻¹*Y*R) • (fun a => χ a) -
      ((1-R)⁻¹*η*X) • (fun a => (χ a)⁻¹) := by
    funext a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rowLocalSum]
    ring
  unfold sexticRowTargetMode
  rw [he, map_sub, map_add, map_add, map_smul, map_smul,
    projection_const χ hχ, projection_geometric χ hχ Y hY,
    projection_character χ hχ, projection_inverse]
  simp only [zero_add, smul_eq_mul, mul_zero, add_zero, mul_one]

/-- Restore the reciprocal local factor from residue samples and known geometric data. -/
def sexticTargetRestoration (χ : MulChar F ℂ) (R Y : ℂ) (f : F → ℂ) : ℂ :=
  1 + (1-R) * (projection χ f - Y^5*(1-Y^6)⁻¹)

/-- Exact restoration removes the geometric term and the completion denominator. -/
theorem sexticTargetRestoration_row (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (Q R η X Y V : ℂ) (hY : 1-Y^6 ≠ 0) (hR : 1-R ≠ 0) :
    sexticTargetRestoration χ R Y (fun a => rowLocalSum Q R η X Y V (χ a)) = 1-η*X := by
  change 1+(1-R)*(sexticRowTargetMode χ Q R η X Y V-Y^5*(1-Y^6)⁻¹)=_
  rw [sexticRowTargetMode_eq χ hχ Q R η X Y V hY]
  have hc := mul_inv_cancel₀ hR
  linear_combination -(η*X)*hc

/-- The restoration error is exactly the completion factor times the projected sample error. -/
theorem sexticTargetRestoration_sub (χ : MulChar F ℂ) (R Y : ℂ) (f g : F → ℂ) :
    sexticTargetRestoration χ R Y f - sexticTargetRestoration χ R Y g =
      (1-R) * projection χ (f-g) := by
  rw [map_sub]
  unfold sexticTargetRestoration
  ring

/-- Uniform residue-sample errors have an explicit stable restoration bound. -/
theorem norm_sexticTargetRestoration_sub_le (χ : MulChar F ℂ) (R Y : ℂ)
    (f g : F → ℂ) (B : ℝ) (h : ∀ a, ‖f a-g a‖ ≤ B) :
    ‖sexticTargetRestoration χ R Y f - sexticTargetRestoration χ R Y g‖ ≤ ‖1-R‖ * B := by
  rw [sexticTargetRestoration_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_projection_le_bound χ (f-g) B h) (norm_nonneg _)

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

/-!
## The inverse sextic projection of the Poisson coefficient series

The projection is taken over actual residue classes at a good Eisenstein prime.
Each sample uses a representative in the literal local Poisson coefficient.
Character orthogonality then extracts the reciprocal target with its phase.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open ArithmeticHarmonicAnalysis.SexticCharacterProjection

variable (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal]
local instance : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _

/-- The character-weighted residue average of the literal local Poisson terms. -/
def sexticProjectedLocalTerm (hlam : lambda ∉ Ideal.span {π}) (η X Y V : ℂ)
    (d : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  (Fintype.card (O ⧸ Ideal.span {π})ˣ : ℂ)⁻¹ *
    ∑ a : O ⧸ Ideal.span {π}, complexSexticChar (Ideal.span {π}) hlam a *
      localTerm π η X Y V (qrep a) 0 d

/-- Residue projection of the convergent Poisson series preserves the inverse-character term. -/
theorem hasSum_sexticProjectedLocalTerm (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    (η X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π η X V‖ < 1) :
    HasSum (sexticProjectedLocalTerm π hlam η X Y V)
      (Y^5*(1-Y^6)⁻¹ - (1-primeR π η X V)⁻¹*η*X) := by
  let χ := complexSexticChar (Ideal.span {π}) hlam
  have hχ : orderOf χ = 6 := CenteredMomentCanonical.complexSexticChar_order_six
    _ hlam (ringChar_ne_two π h2)
  have hsample (a : O ⧸ Ideal.span {π}) :
      HasSum (fun d => χ a * localTerm π η X Y V (qrep a) 0 d)
        (χ a * rowLocalSum (primeQ π) (primeR π η X V) η X Y V (χ a)) := by
    by_cases ha : a=0
    · simpa only [ha, MulChar.map_zero, zero_mul] using
        (hasSum_zero : HasSum (fun _ : Fin 2 × ℕ × ℕ × ℕ => (0 : ℂ)) 0)
    · have hu : qrep a ∉ Ideal.span {π} := by
        intro h
        exact ha (by rw [← mk_qrep a]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h)
      have hn : ‖χ a‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity
        (χ.apply_mem_rootsOfUnity (Units.mk0 a ha))
      have hw : ‖complexSexticChar (Ideal.span {π}) hlam
          (Ideal.Quotient.mk _ (qrep a)) * Y‖ < 1 := by
        rw [mk_qrep, norm_mul, hn, one_mul]
        exact hY
      simpa only [mk_qrep] using
        (hasSum_localTerm_rowLocalSum π hlam h2 hprim η X Y V hu hV hw hR).mul_left (χ a)
  have hs := (hasSum_sum (s := Finset.univ) (fun a _ => hsample a)).mul_left
    (Fintype.card (O ⧸ Ideal.span {π})ˣ : ℂ)⁻¹
  change HasSum (sexticProjectedLocalTerm π hlam η X Y V)
    (sexticRowTargetMode χ (primeQ π) (primeR π η X V) η X Y V) at hs
  have hY6 : 1-Y^6 ≠ 0 := by
    intro he
    have hn : ‖Y^6‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hY (by norm_num)
    rw [← sub_eq_zero.mp he, norm_one] at hn
    exact (lt_irrefl _ hn)
  rwa [sexticRowTargetMode_eq χ hχ _ _ _ _ _ _ hY6] at hs

/-- The exact reciprocal local factor is restored from the literal projected Poisson sum. -/
theorem sexticProjectedLocalTerm_restores_target (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    (η X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π η X V‖ < 1) :
    1 + (1-primeR π η X V) *
      ((∑' d, sexticProjectedLocalTerm π hlam η X Y V d) - Y^5*(1-Y^6)⁻¹) = 1-η*X := by
  rw [(hasSum_sexticProjectedLocalTerm π hlam h2 hprim η X Y V hV hY hR).tsum_eq]
  have hd : 1-primeR π η X V ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hR
    exact lt_irrefl _ hR
  have hc := mul_inv_cancel₀ hd
  linear_combination -(η*X)*hc

/-- The known residue phase restores the reciprocal factor of any specified row. -/
theorem sexticProjectedLocalTerm_restores_row_target (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    (η X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π η X V‖ < 1) (u : O) :
    let ρ := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u)
    1 + ρ⁻¹ * (1-primeR π η X V) *
      ((∑' d, sexticProjectedLocalTerm π hlam η X Y V d) - Y^5*(1-Y^6)⁻¹) =
        1-η*ρ⁻¹*X := by
  dsimp only
  have h := sexticProjectedLocalTerm_restores_target π hlam h2 hprim η X Y V hV hY hR
  linear_combination (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))⁻¹*h

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

/-!
## Stability of sextic target restoration on the floor region

On `Re x ≥ 51/100`, `Re z ≥ 17/50`, the completion parameter has
norm at most `Q^(-11/10)`. Restoration therefore amplifies uniform residue
errors by at most `1 + Q^(-11/10)`, independent of the number of residues.
-/

noncomputable section
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open FamilyContinuationTheory MetaplecticMobiusDescent.Eisenstein

/-- The sextic completion parameter decays uniformly throughout the floor region. -/
theorem norm_sexticCompletion_le_floor {Q : ℝ} (hQ : 1 ≤ Q) {κ x z : ℂ}
    (hκ : ‖κ‖ ≤ 1) (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) :
    ‖κ^6*(Q:ℂ)^4*((Q:ℂ)^(-x))^6*(Q:ℂ)^(-(6*z))‖ ≤ Q^(-(11/10:ℝ)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hX := norm_cpow_neg_eq hQ0 x
  have hV : ‖(Q:ℂ)^(-(6*z))‖ = Q^(-(6*z.re)) := by
    rw [norm_cpow_neg_eq hQ0]
    simp
  have hQ4 : ‖(Q:ℂ)^4‖ = Q^(4:ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hQ0.le, ← Real.rpow_natCast]
    norm_num
  have hpw : (Q^(-x.re))^6 = Q^(-(6*x.re)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    ring
  have hκ6 : ‖κ^6‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hκ
  rw [norm_mul, norm_mul, norm_mul, norm_pow ((Q:ℂ)^(-x)), hX, hV, hQ4, hpw]
  calc
    ‖κ^6‖*Q^(4:ℝ)*Q^(-(6*x.re))*Q^(-(6*z.re))
        ≤ 1*Q^(4:ℝ)*Q^(-(6*x.re))*Q^(-(6*z.re)) := by gcongr
    _ = Q^(4-6*x.re-6*z.re) := by
      rw [one_mul, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
      congr 1
    _ ≤ Q^(-(11/10:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by linarith only [hx, hz])

/-- Explicit stable restoration on the full floor region. -/
theorem norm_sexticTargetRestoration_sub_le_floor {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) {Q : ℝ} (hQ : 1 ≤ Q) {κ x z : ℂ}
    (hκ : ‖κ‖ ≤ 1) (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re)
    (Y : ℂ) (f g : F → ℂ) (B : ℝ) (h : ∀ a, ‖f a-g a‖ ≤ B) :
    let R := κ^6*(Q:ℂ)^4*((Q:ℂ)^(-x))^6*(Q:ℂ)^(-(6*z))
    ‖sexticTargetRestoration χ R Y f - sexticTargetRestoration χ R Y g‖ ≤
      (1+Q^(-(11/10:ℝ)))*B := by
  dsimp only
  have hB : 0 ≤ B := (norm_nonneg (f 0-g 0)).trans (h 0)
  refine (norm_sexticTargetRestoration_sub_le χ _ Y f g B h).trans ?_
  apply mul_le_mul_of_nonneg_right _ hB
  calc
    ‖1-κ^6*(Q:ℂ)^4*((Q:ℂ)^(-x))^6*(Q:ℂ)^(-(6*z))‖
        ≤ ‖(1:ℂ)‖+‖κ^6*(Q:ℂ)^4*((Q:ℂ)^(-x))^6*(Q:ℂ)^(-(6*z))‖ := norm_sub_le _ _
    _ ≤ 1+Q^(-(11/10:ℝ)) := by
      rw [norm_one]
      exact add_le_add (le_refl 1) (norm_sexticCompletion_le_floor hQ hκ hx hz)

/-- The actual Eisenstein-prime completion parameter obeys the same floor bound. -/
theorem norm_primeR_le_floor (π : O) [NeZero π] {η x z : ℂ}
    (hQ : 1 ≤ (Ideal.span {π}).absNorm) (hη : ‖η‖ ≤ 1)
    (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) :
    ‖primeR π η ((primeQ π)^(-x)) ((primeQ π)^(-(6*z)))‖ ≤
      ((Ideal.span {π}).absNorm:ℝ)^(-(11/10:ℝ)) := by
  simpa only [primeR, primeQ, Complex.ofReal_natCast] using
    norm_sexticCompletion_le_floor (Q := ((Ideal.span {π}).absNorm:ℝ))
      (by exact_mod_cast hQ) (norm_primeKappa_le π hη) hx hz

/-- In the critical-strip part of the floor, the actual Poisson series restores the target.
All three convergence inequalities follow from the geometric domain. -/
theorem sexticPoisson_restores_target_on_floor (π : O) [NeZero π]
    [(Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda^2 ∣ π-1)
    {η x z : ℂ} (hη : ‖η‖ ≤ 1)
    (hx : 51/100 ≤ x.re) (hx1 : x.re < 1) (hz : 17/50 ≤ z.re) :
    let X := (primeQ π)^(-x)
    let Y := (primeQ π)^(-(1-x))
    let V := (primeQ π)^(-(6*z))
    1+(1-primeR π η X V)*
      ((∑' d, sexticProjectedLocalTerm π hlam η X Y V d)-Y^5*(1-Y^6)⁻¹) = 1-η*X := by
  have hP0 : Ideal.span {π} ≠ (⊥ : Ideal O) := by
    intro he
    have hm : π ∈ (⊥ : Ideal O) := he ▸ Ideal.subset_span (by simp)
    exact NeZero.ne π (by simpa only [Ideal.mem_bot] using hm)
  have hQ2 := ArtinMertens.two_le_absNorm_of_isPrime
    (inferInstance : (Ideal.span {π}).IsPrime) hP0
  have hQ1 : (1:ℝ) < (Ideal.span {π}).absNorm := by exact_mod_cast (by omega : 1 < (Ideal.span {π}).absNorm)
  have hQ0 : (0:ℝ) < (Ideal.span {π}).absNorm := lt_trans zero_lt_one hQ1
  have hn (t : ℂ) : ‖(primeQ π)^(-t)‖ = ((Ideal.span {π}).absNorm:ℝ)^(-t.re) := by
    simpa only [primeQ, Complex.ofReal_natCast] using norm_cpow_neg_eq hQ0 t
  have hV : ‖(primeQ π)^(-(6*z))‖ < 1 := by
    rw [hn]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ1
    have hz0 : 0 < z.re := by linarith only [hz]
    simpa using neg_neg_iff_pos.mpr (mul_pos (show (0:ℝ)<6 by norm_num) hz0)
  have hY : ‖(primeQ π)^(-(1-x))‖ < 1 := by
    rw [hn]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ1
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hx1]
  have hR : ‖primeR π η ((primeQ π)^(-x)) ((primeQ π)^(-(6*z)))‖ < 1 :=
    (norm_primeR_le_floor π (by omega) hη hx hz).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by norm_num))
  exact sexticProjectedLocalTerm_restores_target π hlam h2 hprim η _ _ _ hV hY hR

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
/-!
## Uniform arithmetic cost over finite prime sets

The restoration denominators have a summable prime-norm majorant. Their
product cost is bounded uniformly in the finite prime set and throughout the
floor region, for the actual Hecke phases.
-/

noncomputable section
open NumberField IsDedekindDomain GaloisForLFunctions.HeckeLFunctions
open scoped BigOperators Classical
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- The completion parameter at an Eisenstein prime with its actual Hecke phase. -/
def sexticPrimeCompletion (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (x z : ℂ)
    (v : HeightOneSpectrum O) : ℂ :=
  (primeKappa (primeGen v) (heckeValue 𝔪 η v.asIdeal))^6 *
    (v.asIdeal.absNorm:ℂ)^4 * ((v.asIdeal.absNorm:ℂ)^(-x))^6 *
    (v.asIdeal.absNorm:ℂ)^(-(6*z))

/-- At every good prime this is precisely the literal Poisson completion parameter. -/
theorem sexticPrimeCompletion_eq_primeR (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (x z : ℂ) (v : HeightOneSpectrum O) (hv : lambda ∉ v.asIdeal) :
    sexticPrimeCompletion 𝔪 η x z v =
      primeR (primeGen v) (heckeValue 𝔪 η v.asIdeal)
        ((v.asIdeal.absNorm:ℂ)^(-x)) ((v.asIdeal.absNorm:ℂ)^(-(6*z))) := by
  rw [primeR, primeQ_primeGen v hv]
  rfl

/-- Floor-region decay for the actual Hecke completion parameter. -/
theorem norm_sexticPrimeCompletion_le_floor (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    {x z : ℂ} (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) (v : HeightOneSpectrum O) :
    ‖sexticPrimeCompletion 𝔪 η x z v‖ ≤ (v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ)) := by
  have hQ := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  simpa only [sexticPrimeCompletion, Complex.ofReal_natCast] using
    norm_sexticCompletion_le_floor (Q := (v.asIdeal.absNorm:ℝ))
      (by exact_mod_cast (by omega : 1 ≤ v.asIdeal.absNorm))
      (norm_primeKappa_le (primeGen v) (norm_heckeValue_le_one 𝔪 η _)) hx hz

/-- A finite uniform bound for the arithmetic cost of all restoration denominators. -/
def sexticRestorationBound : ℝ :=
  Real.exp (∑' v : HeightOneSpectrum O, (v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ)))

theorem sexticRestorationBound_pos : 0 < sexticRestorationBound := Real.exp_pos _

/-- The denominator-restoration cost stays bounded as the set of primes grows. -/
theorem prod_norm_sexticRestoration_le (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    {x z : ℂ} (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re)
    (S : Finset (HeightOneSpectrum O)) :
    ∏ v ∈ S, ‖1-sexticPrimeCompletion 𝔪 η x z v‖ ≤ sexticRestorationBound := by
  have hsum := numberField_summable_finitePlace_absNorm_rpow (K := K)
    (σ := (11/10:ℝ)) (by norm_num)
  have hp : ∏ v ∈ S, ‖1-sexticPrimeCompletion 𝔪 η x z v‖ ≤
      Real.exp (∑ v ∈ S, (v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ))) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod (fun v _ => norm_nonneg _)
    intro v _
    calc
      ‖1-sexticPrimeCompletion 𝔪 η x z v‖ ≤ ‖(1:ℂ)‖+‖sexticPrimeCompletion 𝔪 η x z v‖ := norm_sub_le _ _
      _ ≤ 1+(v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ)) := by
        rw [norm_one]
        exact add_le_add (le_refl 1) (norm_sexticPrimeCompletion_le_floor 𝔪 η hx hz v)
      _ ≤ Real.exp ((v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ))) := by
        simpa only [add_comm] using Real.add_one_le_exp ((v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ)))
  refine hp.trans (Real.exp_le_exp.mpr ?_)
  exact hsum.sum_le_tsum S (fun v _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

/-!
## Nonvanishing of the infinite restoration factor

The same prime-norm majorant makes both completion products converge. Since
every local completion parameter has norm at most one half, their products
are inverses. The normalization therefore introduces no zero of its own.
-/

noncomputable section
open NumberField IsDedekindDomain GaloisForLFunctions.HeckeLFunctions
open scoped BigOperators Classical
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- Every arithmetic completion parameter lies in the closed half-unit disk on the floor. -/
theorem norm_sexticPrimeCompletion_le_half (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    {x z : ℂ} (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) (v : HeightOneSpectrum O) :
    ‖sexticPrimeCompletion 𝔪 η x z v‖ ≤ 1/2 := by
  have hQ : (2:ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  calc
    ‖sexticPrimeCompletion 𝔪 η x z v‖ ≤ (v.asIdeal.absNorm:ℝ)^(-(11/10:ℝ)) :=
      norm_sexticPrimeCompletion_le_floor 𝔪 η hx hz v
    _ ≤ (v.asIdeal.absNorm:ℝ)^(-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hQ]) (by norm_num)
    _ = (v.asIdeal.absNorm:ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1/2 := by
      rw [inv_le_comm₀ (by linarith only [hQ]) (by norm_num)]
      linarith only [hQ]

/-- Absolute summability of the actual Hecke completion parameters on the floor. -/
theorem summable_norm_sexticPrimeCompletion (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    {x z : ℂ} (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) :
    Summable (fun v : HeightOneSpectrum O => ‖sexticPrimeCompletion 𝔪 η x z v‖) :=
  (numberField_summable_finitePlace_absNorm_rpow (K := K)
    (σ := (11/10:ℝ)) (by norm_num)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_sexticPrimeCompletion_le_floor 𝔪 η hx hz)

/-- Primes where the unramified sextic Poisson identities apply. -/
abbrev SexticPoissonPrime :=
  {v : HeightOneSpectrum O // lambda ∉ v.asIdeal ∧ (2 : O) ∉ v.asIdeal}

/-- The projected Poisson series with the actual Hecke value at a good prime. -/
def sexticHeckeProjectedLocalTerm (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (v : SexticPoissonPrime) (x z : ℂ) (d : Fin 2 × ℕ × ℕ × ℕ) : ℂ := by
  letI := isMaximal_span_primeGen v.1 v.2.1
  have hλ : lambda ∉ Ideal.span {primeGen v.1} := (primeGen_spec v.1 v.2.1).1 ▸ v.2.1
  exact sexticProjectedLocalTerm (primeGen v.1) hλ (heckeValue 𝔪 η v.1.asIdeal)
    ((v.1.asIdeal.absNorm:ℂ)^(-x)) ((v.1.asIdeal.absNorm:ℂ)^(-(1-x)))
    ((v.1.asIdeal.absNorm:ℂ)^(-(6*z))) d

/-- The actual Hecke local factor is recovered throughout the critical-strip floor. -/
theorem sexticHeckePoisson_restores_target_on_floor (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (v : SexticPoissonPrime) {x z : ℂ}
    (hx : 51/100 ≤ x.re) (hx1 : x.re < 1) (hz : 17/50 ≤ z.re) :
    let X := (v.1.asIdeal.absNorm:ℂ)^(-x)
    let Y := (v.1.asIdeal.absNorm:ℂ)^(-(1-x))
    1+(1-sexticPrimeCompletion 𝔪 η x z v.1)*
      ((∑' d, sexticHeckeProjectedLocalTerm 𝔪 η v x z d)-Y^5*(1-Y^6)⁻¹) =
        1-heckeValue 𝔪 η v.1.asIdeal*X := by
  letI := isMaximal_span_primeGen v.1 v.2.1
  have hspan := primeGen_spec v.1 v.2.1
  have hλ : lambda ∉ Ideal.span {primeGen v.1} := hspan.1 ▸ v.2.1
  have h2 : (2:O) ∉ Ideal.span {primeGen v.1} := hspan.1 ▸ v.2.2
  have h := sexticPoisson_restores_target_on_floor (primeGen v.1) hλ h2 hspan.2
    (norm_heckeValue_le_one 𝔪 η v.1.asIdeal) hx hx1 hz
  simpa only [sexticHeckeProjectedLocalTerm, sexticPrimeCompletion, primeR,
    primeQ_primeGen v.1 v.2.1] using h

/-- Forward and inverse restoration factors both converge and are exact inverses. -/
theorem sexticCompletion_products_inverse (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    {x z : ℂ} (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) :
    Multipliable (fun v : SexticPoissonPrime => 1-sexticPrimeCompletion 𝔪 η x z v.1) ∧
    Multipliable (fun v : SexticPoissonPrime => (1-sexticPrimeCompletion 𝔪 η x z v.1)⁻¹) ∧
    (∏' v : SexticPoissonPrime, (1-sexticPrimeCompletion 𝔪 η x z v.1)) *
      (∏' v : SexticPoissonPrime, (1-sexticPrimeCompletion 𝔪 η x z v.1)⁻¹) = 1 := by
  have hs := (summable_norm_sexticPrimeCompletion 𝔪 η hx hz).subtype
    (fun v => lambda ∉ v.asIdeal ∧ (2 : O) ∉ v.asIdeal)
  have hf := multipliable_one_sub hs
  have hi := multipliable_one_sub_inv hs (fun v => norm_sexticPrimeCompletion_le_half 𝔪 η hx hz v.1)
  refine ⟨hf, hi, ?_⟩
  have hn (v : SexticPoissonPrime) : 1-sexticPrimeCompletion 𝔪 η x z v.1 ≠ 0 := by
    intro he
    have h := norm_sexticPrimeCompletion_le_half 𝔪 η hx hz v.1
    rw [← sub_eq_zero.mp he, norm_one] at h
    norm_num at h
  rw [← hf.tprod_mul hi]
  simp only [mul_inv_cancel₀ (hn _), tprod_one]

/-- Infinite restoration cannot erase a target by contributing a zero factor. -/
theorem sexticCompletion_tprod_ne_zero (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    {x z : ℂ} (hx : 51/100 ≤ x.re) (hz : 17/50 ≤ z.re) :
    (∏' v : SexticPoissonPrime, (1-sexticPrimeCompletion 𝔪 η x z v.1)) ≠ 0 := by
  have h := (sexticCompletion_products_inverse 𝔪 η hx hz).2.2
  intro he
  rw [he, zero_mul] at h
  exact zero_ne_one h

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
