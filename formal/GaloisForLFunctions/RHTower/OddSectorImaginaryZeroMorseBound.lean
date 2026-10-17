import GaloisForLFunctions.RHTower.OddSectorGroundSpectralQuotient
import GaloisForLFunctions.HTGeometry.CompactFormNegativeCapacity

/-!
# Imaginary ground zeros and opposite-parity negative directions

Multiplication of an odd paired ground divisor by frequency is an actual
same-aperture even form vector. Its corrected energy is the squared node
times the positive divisor energy. Imaginary nodes therefore expose
negative directions in the opposite parity of the same arithmetic pencil.
-/

open Complex Set Filter Topology
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature

/-- Paired division supplies one full frequency derivative in the complete
form domain; its parity is even. -/
theorem exists_even_frequency_lift_of_paired_divisor (a : SuzukiPositiveAperture)
    (G v : CCMArchimedeanFormDomain a)
    (hv : ccmArchimedeanFormReflection a v = -v) (z : ℂ)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w) :
    ∃ h : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a h = h ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a h) w = w*unitaryLaplace (timeRep a v) w := by
  have hGz : unitaryLaplace (timeRep a G) z = 0 := by rw [hfac,sub_self,zero_mul]
  obtain ⟨p,hp⟩ := exists_div a G hGz
  let h := p-z • v
  have hc (x : CCMArchimedeanFormDomain a) : Continuous (unitaryLaplace (timeRep a x)) :=
    (CCMXiStrip.differentiable_unitaryLaplace a.2.le
      (integrable_timeRep a x) (supportedIn_timeRep a x)).continuous
  have hfun : unitaryLaplace (timeRep a h) =
      fun w : ℂ => w*unitaryLaplace (timeRep a v) w := by
    apply Continuous.ext_on (dense_univ.sdiff_finite (finite_singleton z))
      (hc h) (continuous_id.mul (hc v))
    intro w hw
    have hwz : w ≠ z := hw.2
    change (evalAt a w) (p-z • v) = w*unitaryLaplace (timeRep a v) w
    rw [map_sub,map_smul]
    simp only [evalAt_apply]
    rw [hp w hwz,hfac]
    field_simp [sub_ne_zero.mpr hwz]
    ring
  refine ⟨h,?_,fun w => congrFun hfun w⟩
  apply eq_of_transform_eq a
  intro t
  rw [CCMEvenSector.unitaryLaplace_reflection,hfun]
  change (-(t : ℂ))*unitaryLaplace (timeRep a v) (-(t : ℂ)) =
    (t : ℂ)*unitaryLaplace (timeRep a v) (t : ℂ)
  rw [odd_transform_neg a hv]
  ring

/-- Frequency multiplication transfers the complete signed form, including
its prime and polar terms. -/
theorem arithmeticShiftedForm_frequency_lifts (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (v₁ v₂ h₁ h₂ : CCMArchimedeanFormDomain a) (z : ℂ)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v₂) w)
    (hh₁ : ∀ w : ℂ, unitaryLaplace (timeRep a h₁) w = w*unitaryLaplace (timeRep a v₁) w)
    (hh₂ : ∀ w : ℂ, unitaryLaplace (timeRep a h₂) w = w*unitaryLaplace (timeRep a v₂) w) :
    arithmeticShiftedForm a h₁ h₂ = z^2*arithmeticShiftedForm a v₁ v₂ := by
  have he : arithmeticShiftedForm a h₁ h₂ = arithmeticShiftedForm a v₁ (G+z^2 • v₂) := by
    apply arithmeticShiftedForm_eq_of_transform_products
    intro w
    rw [hh₁,hh₂,unitaryLaplace_timeRep_add_smul,hfac]
    simp only [map_mul,Complex.conj_conj]
    ring
  rw [he,arithmeticShiftedForm_add_right,arithmeticShiftedForm_ground_right a hG,
    arithmeticShiftedForm_smul_right,zero_add]

/-- Each nonzero imaginary generator zero has a literal even negative
direction for the same arithmetic-corrected shifted form. -/
theorem exists_even_negative_of_oddGround_imaginary_zero (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) = 0) :
    ∃ h : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a h = h ∧
      (arithmeticShiftedForm a h h).re < 0 := by
  have hz0 : I*(b : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')
  obtain ⟨v,hv,hfac⟩ := exists_odd_paired_div a hG.1.2 hz0 hz
  obtain ⟨h,heven,hh⟩ := exists_even_frequency_lift_of_paired_divisor a G v hv _ hfac
  refine ⟨h,heven,?_⟩
  rw [arithmeticShiftedForm_frequency_lifts a hG.1 v v h h _ hfac hh hh]
  have hzsq : (I*(b : ℂ))^2 = ((-b^2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow,I_sq]
    ring
  rw [hzsq,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hp := oddGroundGenerator_quotient_pos a hG hv (I*(b : ℂ)) hfac
  have hprod := mul_pos (sq_pos_of_pos hb) hp
  nlinarith

/-- Distinct real squared nodes give orthogonal raw ground divisors, before
normalization of their cardinal coordinates. -/
theorem groundDivisors_form_orthogonal (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (v₁ v₂ : CCMArchimedeanFormDomain a) (z₁ z₂ : ℂ)
    (hc : conj (z₁^2) = z₁^2) (hne : z₁^2 ≠ z₂^2)
    (h₁ : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z₁^2)*unitaryLaplace (timeRep a v₁) w)
    (h₂ : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z₂^2)*unitaryLaplace (timeRep a v₂) w) :
    arithmeticShiftedForm a v₁ v₂ = 0 := by
  have ht (w : ℂ) : unitaryLaplace (timeRep a (G+(z₂^2-z₁^2) • v₂)) w =
      (w^2-z₁^2)*unitaryLaplace (timeRep a v₂) w := by
    rw [unitaryLaplace_timeRep_add_smul,h₂]
    ring
  have he := arithmeticShiftedForm_quadratic_transfer a G (G+(z₂^2-z₁^2) • v₂)
    v₁ v₂ hc h₁ ht
  rw [arithmeticShiftedForm_ground_left a hG,arithmeticShiftedForm_add_right,
    arithmeticShiftedForm_ground_right a hG,arithmeticShiftedForm_smul_right,zero_add] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (sub_ne_zero.mpr hne.symm)

/-- Distinct positive imaginary zeros realize a negative diagonal block in
the actual even sector, without a finite-dimensional source ansatz. -/
theorem exists_even_negative_family_of_oddGround_zeros (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (m : ℕ) (b : Fin m → ℝ) (hinj : Function.Injective b)
    (hb : ∀ i, 0 < b i)
    (hz : ∀ i, unitaryLaplace (timeRep a G) (I*((b i : ℝ) : ℂ)) = 0) :
    ∃ h : Fin m → CCMArchimedeanFormDomain a,
      (∀ i, ccmArchimedeanFormReflection a (h i) = h i) ∧
      (∀ i, (arithmeticShiftedForm a (h i) (h i)).re < 0) ∧
      ∀ i j, i ≠ j → arithmeticShiftedForm a (h i) (h j) = 0 := by
  have hdiv (i : Fin m) := exists_odd_paired_div a hG.1.2
    (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (hb i).ne')) (hz i)
  choose v hv hfac using hdiv
  choose h heven hfreq using fun i =>
    exists_even_frequency_lift_of_paired_divisor a G (v i) (hv i) _ (hfac i)
  have hsquare (i : Fin m) : (I*((b i : ℝ) : ℂ))^2 = ((-(b i)^2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow,I_sq]
    ring
  refine ⟨h,heven,?_,?_⟩
  · intro i
    rw [arithmeticShiftedForm_frequency_lifts a hG.1 (v i) (v i) (h i) (h i)
      _ (hfac i) (hfreq i) (hfreq i),hsquare,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    have hp := oddGroundGenerator_quotient_pos a hG (hv i) _ (hfac i)
    have hprod := mul_pos (sq_pos_of_pos (hb i)) hp
    nlinarith
  · intro i j hij
    have hne : (I*((b i : ℝ) : ℂ))^2 ≠ (I*((b j : ℝ) : ℂ))^2 := by
      intro he
      rw [hsquare,hsquare] at he
      have hr := congrArg Complex.re he
      simp only [Complex.ofReal_re] at hr
      have hs : (b i)^2 = (b j)^2 := neg_injective hr
      exact hij (hinj ((sq_eq_sq₀ (hb i).le (hb j).le).mp hs))
    have hc : conj ((I*((b i : ℝ) : ℂ))^2) = (I*((b i : ℝ) : ℂ))^2 := by
      rw [hsquare,Complex.conj_ofReal]
    rw [arithmeticShiftedForm_frequency_lifts a hG.1 (v i) (v j) (h i) (h j)
      _ (hfac j) (hfreq i) (hfreq j),
      groundDivisors_form_orthogonal a hG.1 (v i) (v j) _ _ hc hne (hfac i) (hfac j),mul_zero]

/-- One finite capacity bounds every family of distinct imaginary ground
zeros; compactness supplies the capacity unconditionally. -/
theorem exists_oddGround_imaginary_zero_capacity (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G) :
    ∃ n : ℕ, ∀ m : ℕ, ∀ b : Fin m → ℝ, Function.Injective b →
      (∀ i, 0 < b i) →
      (∀ i, unitaryLaplace (timeRep a G) (I*((b i : ℝ) : ℂ)) = 0) → m ≤ n := by
  obtain ⟨n,hn⟩ := GaloisForLFunctions.HTGeometry.exists_negative_orthogonal_family_bound
    (arithmeticGroundCompact a) (arithmeticGroundCompact_isCompact a)
  refine ⟨n,fun m b hinj hb hz => ?_⟩
  obtain ⟨h,_heven,hneg,horth⟩ :=
    exists_even_negative_family_of_oddGround_zeros a hG m b hinj hb hz
  apply hn m h
  · intro i
    rw [inner_identity_sub_groundCompact]
    exact hneg i
  · intro i j hij
    rw [inner_identity_sub_groundCompact]
    exact horth i j hij

/-- **Finite imaginary-zero obstruction.** The canonical odd generator has
only finitely many positive imaginary zeros. -/
theorem oddGround_positive_imaginary_zeros_finite (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G) :
    Set.Finite {b : ℝ | 0 < b ∧ unitaryLaplace (timeRep a G) (I*(b : ℂ)) = 0} := by
  classical
  obtain ⟨n,hn⟩ := exists_oddGround_imaginary_zero_capacity a hG
  by_contra hfin
  have hinf : {b : ℝ | 0 < b ∧ unitaryLaplace (timeRep a G) (I*(b : ℂ)) = 0}.Infinite := hfin
  let f := hinf.natEmbedding _
  let b : Fin (n+1) → ℝ := fun i => (f i.val).val
  have hbinj : Function.Injective b := by
    intro i j hij
    apply Fin.ext
    apply f.injective
    exact Subtype.ext hij
  have hbound := hn (n+1) b hbinj (fun i => (f i.val).property.1)
    (fun i => (f i.val).property.2)
  omega

/-- At every positive aperture an actual canonical odd ground generator has
only finitely many nonreal zeros. The cross-axis law and oddness identify
every exceptional zero with one of the finitely many imaginary pairs. -/
theorem exists_oddGround_generator_finite_nonreal_zeros (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a, IsOddArithmeticGroundGenerator a G ∧
      (∀ z : ℂ, unitaryLaplace (timeRep a G) z = 0 → z.re = 0 ∨ z.im = 0) ∧
      Set.Finite {z : ℂ | unitaryLaplace (timeRep a G) z = 0 ∧ z.im ≠ 0} := by
  obtain ⟨G,hG,hcross,_hcanonical⟩ := exists_canonical_oddArithmeticGround_generator a
  let S : Set ℝ := {b | 0 < b ∧ unitaryLaplace (timeRep a G) (I*(b : ℂ)) = 0}
  have hS : S.Finite := oddGround_positive_imaginary_zeros_finite a hG
  refine ⟨G,hG,hcross,?_⟩
  apply ((hS.image (fun b : ℝ => I*(b : ℂ))).union
    (hS.image (fun b : ℝ => -(I*(b : ℂ))))).subset
  intro z hz
  have hre : z.re = 0 := (hcross z hz.1).resolve_right hz.2
  by_cases hb : 0 < z.im
  · have hrep : I*(z.im : ℂ) = z := by apply Complex.ext <;> simp [hre]
    exact Or.inl ⟨z.im,⟨hb,by rw [hrep]; exact hz.1⟩,hrep⟩
  · have hbn : 0 < -z.im := by
      by_contra hn
      have he : z.im = 0 := by linarith
      exact hz.2 he
    have hrep : -(I*((-z.im : ℝ) : ℂ)) = z := by apply Complex.ext <;> simp [hre]
    refine Or.inr ⟨-z.im,⟨hbn,?_⟩,hrep⟩
    have hnrep : I*((-z.im : ℝ) : ℂ) = -z := by
      simpa only [neg_neg] using congrArg Neg.neg hrep
    rw [hnrep,odd_transform_neg a hG.1.2,hz.1,neg_zero]

end RHTower.OddSector
