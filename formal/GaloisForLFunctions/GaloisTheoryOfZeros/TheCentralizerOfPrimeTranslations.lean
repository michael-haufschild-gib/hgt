import GaloisForLFunctions.GaloisTheoryOfZeros.ThePrimeTimePointsOfTheZeroMotive
import GaloisForLFunctions.HTGeometry.WeldClassTable

/-!
# The centralizer of prime translations

Translations by the prime-time points at two and three have distinct joint
spectra on the full integer zero group. Their entire complex-linear centralizer
consists of diagonal coefficient multipliers. Its algebra endomorphisms are
exactly translations by motive points, hence are automatically invertible.
Fixing the identity point reduces this centralizer to the identity.

The same spectral separation makes the full coordinate algebra difference-simple:
its only ideals stable under both prime translations are zero and the whole
algebra. Every nonnegative two-prime orbit through every complex motive point
is consequently Zariski dense. These statements concern the entire zero group,
with no height bound or independence assumption on the zeros.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- A multiplier on every actual exponent defines a linear operator on the full zero algebra. -/
def zeroMotiveDiagonal (c : rawZeroRelationGroup → ℂ) :
    ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra where
  toFun f := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support
    (fun z => c z*f.coeff z) (by
      intro z hz
      exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hz).2))
  map_add' f g := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro z
    change c z*(f.coeff z+g.coeff z) = c z*f.coeff z+c z*g.coeff z
    exact mul_add _ _ _
  map_smul' a f := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro z
    change c z*(a*f.coeff z) = a*(c z*f.coeff z)
    ring

/-- Diagonal multipliers act coefficientwise, without a support bound. -/
theorem zeroMotiveDiagonal_coeff (c : rawZeroRelationGroup → ℂ)
    (f : ZeroMotiveAlgebra) (z : rawZeroRelationGroup) :
    (zeroMotiveDiagonal c f).coeff z = c z*f.coeff z := rfl

theorem zeroMotiveDiagonal_single (c : rawZeroRelationGroup → ℂ)
    (z : rawZeroRelationGroup) (a : ℂ) :
    zeroMotiveDiagonal c (AddMonoidAlgebra.single z a) = AddMonoidAlgebra.single z (c z*a) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro w
  by_cases h : z = w
  · subst w
    simp only [zeroMotiveDiagonal_coeff,AddMonoidAlgebra.coeff_single,Finsupp.single_eq_same]
  · simp only [zeroMotiveDiagonal_coeff,AddMonoidAlgebra.coeff_single,Finsupp.single_eq_of_ne (Ne.symm h),mul_zero]

/-- The multiplier is recovered by reading the coefficient of each character. -/
theorem zeroMotiveDiagonal_injective : Function.Injective zeroMotiveDiagonal := by
  intro c d h
  funext z
  have he := congrArg (fun L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra =>
    (L (AddMonoidAlgebra.single z 1)).coeff z) h
  simpa only [zeroMotiveDiagonal_coeff,AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same,mul_one] using he

private def translatedZeroBasis (χ : RawZeroMotivePoint) :
    Multiplicative rawZeroRelationGroup →* ZeroMotiveAlgebra where
  toFun z := AddMonoidAlgebra.single z.toAdd ((χ z.toAdd).toMul : ℂ)
  map_one' := by
    change AddMonoidAlgebra.single 0 ((χ 0).toMul : ℂ) = 1
    rw [map_zero]
    rfl
  map_mul' z w := by
    change AddMonoidAlgebra.single (z.toAdd+w.toAdd) ((χ (z.toAdd+w.toAdd)).toMul : ℂ) = _
    rw [map_add,AddMonoidAlgebra.single_mul_single]
    rfl

/-- Translation by a complex point of the full zero motive. -/
def zeroMotiveTranslation (χ : RawZeroMotivePoint) :
    ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra :=
  AddMonoidAlgebra.lift ℂ ZeroMotiveAlgebra rawZeroRelationGroup (translatedZeroBasis χ)

theorem zeroMotiveTranslation_single (χ : RawZeroMotivePoint)
    (z : rawZeroRelationGroup) (a : ℂ) :
    zeroMotiveTranslation χ (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single z (a*((χ z).toMul : ℂ)) := by
  rw [zeroMotiveTranslation,AddMonoidAlgebra.lift_single]
  change a • AddMonoidAlgebra.single z ((χ z).toMul : ℂ) = _
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul]

/-- Translation is the diagonal multiplier supplied by its character values. -/
theorem zeroMotiveTranslation_diagonal (χ : RawZeroMotivePoint) :
    (zeroMotiveTranslation χ).toLinearMap = zeroMotiveDiagonal (fun z => ((χ z).toMul : ℂ)) := by
  apply (AddMonoidAlgebra.basis rawZeroRelationGroup ℂ).ext
  intro z
  simp only [AddMonoidAlgebra.basis_apply,AlgHom.toLinearMap_apply,
    zeroMotiveTranslation_single,zeroMotiveDiagonal_single,one_mul,mul_one]

/-- Prime Frobenius acts on regular functions by translation through the prime-time point. -/
def zeroMotivePrimeTranslation (p : ℕ) : ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra :=
  zeroMotiveTranslation (rawZeroMotiveFlow (Real.log p))

/-- The prime translation eigenvalue of an actual character exponent. -/
def zeroPrimeEigenvalue (p : ℕ) (z : rawZeroRelationGroup) : ℂ :=
  Complex.exp ((Real.log p : ℂ)*(z : ℂ))

theorem zeroMotivePrimeTranslation_coeff (p : ℕ) (f : ZeroMotiveAlgebra)
    (z : rawZeroRelationGroup) :
    (zeroMotivePrimeTranslation p f).coeff z = zeroPrimeEigenvalue p z*f.coeff z := by
  have h := congrArg (fun L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra => (L f).coeff z)
    (zeroMotiveTranslation_diagonal (rawZeroMotiveFlow (Real.log p)))
  exact h


/-- No nonzero complex exponent is a period of two distinct prime clocks. -/
theorem exponent_eq_zero_of_two_prime_periods {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {z : ℂ}
    (h₁ : Complex.exp ((Real.log p : ℂ)*z) = 1)
    (h₂ : Complex.exp ((Real.log q : ℂ)*z) = 1) : z = 0 := by
  obtain ⟨a,ha⟩ := Complex.exp_eq_one_iff.mp h₁
  obtain ⟨b,hb⟩ := Complex.exp_eq_one_iff.mp h₂
  have hperiod : (2*(Real.pi : ℂ)*I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he : ((a : ℂ)*(Real.log q : ℂ)-(b : ℂ)*(Real.log p : ℂ)) *
      (2*(Real.pi : ℂ)*I) = 0 := by
    linear_combination (Real.log p : ℂ)*hb-(Real.log q : ℂ)*ha
  have hc := (mul_eq_zero.mp he).resolve_right hperiod
  have hr : (a : ℝ)*Real.log q-(b : ℝ)*Real.log p = 0 := by
    have h := congrArg Complex.re hc
    simpa only [Complex.sub_re,Complex.mul_re,Complex.intCast_re,Complex.intCast_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.zero_re] using h
  have hab := GaloisForLFunctions.RHTower.two_prime_log_indep hp hq hpq (-b) a (by
    push_cast
    linear_combination hr)
  rw [hab.2,Int.cast_zero,zero_mul] at ha
  have hlog : (Real.log p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  exact (mul_eq_zero.mp ha).resolve_left hlog

/-- The two prime exponential coordinates distinguish all complex exponents. -/
theorem two_prime_exponential_injective {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (fun z : ℂ =>
      (Complex.exp ((Real.log p : ℂ)*z),Complex.exp ((Real.log q : ℂ)*z))) := by
  intro z w h
  apply sub_eq_zero.mp
  apply exponent_eq_zero_of_two_prime_periods hp hq hpq
  · have he : Complex.exp ((Real.log p : ℂ)*z) = Complex.exp ((Real.log p : ℂ)*w) :=
      congrArg Prod.fst h
    rw [mul_sub,Complex.exp_sub,he,div_self (Complex.exp_ne_zero _)]
  · have he : Complex.exp ((Real.log q : ℂ)*z) = Complex.exp ((Real.log q : ℂ)*w) :=
      congrArg Prod.snd h
    rw [mul_sub,Complex.exp_sub,he,div_self (Complex.exp_ne_zero _)]

/-- Every exponent in the entire zero group has a distinct joint prime spectrum. -/
theorem zeroPrimeEigenvalue_pair_injective : Function.Injective
    (fun z : rawZeroRelationGroup => (zeroPrimeEigenvalue 2 z,zeroPrimeEigenvalue 3 z)) := by
  intro z w h
  apply Subtype.ext
  exact two_prime_exponential_injective Nat.prime_two Nat.prime_three (by norm_num) h

/-- Basis characters are eigenvectors of each prime translation. -/
theorem zeroMotivePrimeTranslation_basis (p : ℕ) (z : rawZeroRelationGroup) :
    zeroMotivePrimeTranslation p (AddMonoidAlgebra.single z 1) =
      zeroPrimeEigenvalue p z • AddMonoidAlgebra.single z 1 := by
  rw [zeroMotivePrimeTranslation,zeroMotiveTranslation_single,
    AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one,one_mul]
  rfl

/-- The joint eigenspace indexed by an exponent is exactly its character line. -/
theorem zeroMotive_joint_eigenvector (z : rawZeroRelationGroup) (f : ZeroMotiveAlgebra)
    (h₂ : zeroMotivePrimeTranslation 2 f = zeroPrimeEigenvalue 2 z • f)
    (h₃ : zeroMotivePrimeTranslation 3 f = zeroPrimeEigenvalue 3 z • f) :
    f = AddMonoidAlgebra.single z (f.coeff z) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro w
  by_cases hwz : z = w
  · subst w
    simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_eq_same]
  · have hw : f.coeff w = 0 := by
      by_contra hn
      have he₂ := congrArg (fun a : ZeroMotiveAlgebra => a.coeff w) h₂
      have he₃ := congrArg (fun a : ZeroMotiveAlgebra => a.coeff w) h₃
      rw [zeroMotivePrimeTranslation_coeff] at he₂ he₃
      change zeroPrimeEigenvalue 2 w*f.coeff w = zeroPrimeEigenvalue 2 z*f.coeff w at he₂
      change zeroPrimeEigenvalue 3 w*f.coeff w = zeroPrimeEigenvalue 3 z*f.coeff w at he₃
      have he : w = z := zeroPrimeEigenvalue_pair_injective
        (Prod.ext (mul_right_cancel₀ hn he₂) (mul_right_cancel₀ hn he₃))
      exact hwz he.symm
    simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_eq_of_ne (Ne.symm hwz),hw]

/-- Commutation with the two prime translations on every regular function. -/
def CommutesWithPrimeTranslations (L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra) : Prop :=
  (∀ f, L (zeroMotivePrimeTranslation 2 f) = zeroMotivePrimeTranslation 2 (L f)) ∧
  (∀ f, L (zeroMotivePrimeTranslation 3 f) = zeroMotivePrimeTranslation 3 (L f))

/-- A commuting linear map preserves every individual character line. -/
theorem primeTranslation_commutant_basis (L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra)
    (h : CommutesWithPrimeTranslations L) (z : rawZeroRelationGroup) :
    L (AddMonoidAlgebra.single z 1) =
      AddMonoidAlgebra.single z ((L (AddMonoidAlgebra.single z 1)).coeff z) := by
  apply zeroMotive_joint_eigenvector
  · rw [← h.1,zeroMotivePrimeTranslation_basis,map_smul]
  · rw [← h.2,zeroMotivePrimeTranslation_basis,map_smul]

/-- Every diagonal multiplier commutes with both prime translations. -/
theorem zeroMotiveDiagonal_commutes (c : rawZeroRelationGroup → ℂ) :
    CommutesWithPrimeTranslations (zeroMotiveDiagonal c) := by
  have h (p : ℕ) (f : ZeroMotiveAlgebra) :
      zeroMotiveDiagonal c (zeroMotivePrimeTranslation p f) =
        zeroMotivePrimeTranslation p (zeroMotiveDiagonal c f) := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro z
    simp only [zeroMotiveDiagonal_coeff,zeroMotivePrimeTranslation_coeff]
    ring
  exact ⟨h 2,h 3⟩

/-- The full linear centralizer consists uniquely of arbitrary diagonal multipliers. -/
theorem primeTranslation_linear_centralizer (L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra) :
    CommutesWithPrimeTranslations L ↔
      ∃! c : rawZeroRelationGroup → ℂ, L = zeroMotiveDiagonal c := by
  constructor
  · intro h
    let c : rawZeroRelationGroup → ℂ := fun z => (L (AddMonoidAlgebra.single z 1)).coeff z
    have he : L = zeroMotiveDiagonal c := by
      apply (AddMonoidAlgebra.basis rawZeroRelationGroup ℂ).ext
      intro z
      simp only [AddMonoidAlgebra.basis_apply,zeroMotiveDiagonal_single,mul_one]
      exact primeTranslation_commutant_basis L h z
    refine ⟨c,he,?_⟩
    intro d hd
    exact zeroMotiveDiagonal_injective (hd.symm.trans he)
  · rintro ⟨c,rfl,_⟩
    exact zeroMotiveDiagonal_commutes c


/-- Translation multiplies each coefficient by its character value. -/
theorem zeroMotiveTranslation_coeff (χ : RawZeroMotivePoint)
    (f : ZeroMotiveAlgebra) (z : rawZeroRelationGroup) :
    (zeroMotiveTranslation χ f).coeff z = ((χ z).toMul : ℂ)*f.coeff z :=
  congrArg (fun L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra => (L f).coeff z)
    (zeroMotiveTranslation_diagonal χ)

/-- Distinct motive points give distinct translation operators. -/
theorem zeroMotiveTranslation_injective : Function.Injective zeroMotiveTranslation := by
  intro χ ψ h
  apply AddMonoidHom.ext
  intro z
  apply Additive.toMul.injective
  apply Units.ext
  have he := congrArg (fun F : ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra =>
    (F (AddMonoidAlgebra.single z 1)).coeff z) h
  simpa only [zeroMotiveTranslation_coeff,AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same,mul_one] using he

/-- Composition of translations is multiplication of motive points. -/
theorem zeroMotiveTranslation_add (χ ψ : RawZeroMotivePoint) :
    zeroMotiveTranslation (χ+ψ) = (zeroMotiveTranslation χ).comp (zeroMotiveTranslation ψ) := by
  apply (AddMonoidAlgebra.lift ℂ ZeroMotiveAlgebra rawZeroRelationGroup).symm.injective
  apply MonoidHom.ext
  intro z
  change zeroMotiveTranslation (χ+ψ) (AddMonoidAlgebra.single z.toAdd 1) =
    zeroMotiveTranslation χ (zeroMotiveTranslation ψ (AddMonoidAlgebra.single z.toAdd 1))
  simp only [zeroMotiveTranslation_single,one_mul]
  change AddMonoidAlgebra.single z.toAdd (((χ z.toAdd).toMul : ℂ)*((ψ z.toAdd).toMul : ℂ)) = _
  rw [mul_comm]

/-- The identity point acts trivially on regular functions. -/
theorem zeroMotiveTranslation_zero : zeroMotiveTranslation 0 = AlgHom.id ℂ ZeroMotiveAlgebra := by
  apply (AddMonoidAlgebra.lift ℂ ZeroMotiveAlgebra rawZeroRelationGroup).symm.injective
  apply MonoidHom.ext
  intro z
  change zeroMotiveTranslation 0 (AddMonoidAlgebra.single z.toAdd 1) = _
  rw [zeroMotiveTranslation_single]
  change AddMonoidAlgebra.single z.toAdd (1*1 : ℂ) = AddMonoidAlgebra.single z.toAdd 1
  rw [one_mul]

/-- Every translation is invertible, with inverse given by the opposite character. -/
theorem zeroMotiveTranslation_bijective (χ : RawZeroMotivePoint) :
    Function.Bijective (zeroMotiveTranslation χ) := by
  have hl (f : ZeroMotiveAlgebra) : zeroMotiveTranslation (-χ) (zeroMotiveTranslation χ f) = f := by
    change ((zeroMotiveTranslation (-χ)).comp (zeroMotiveTranslation χ)) f = f
    rw [← zeroMotiveTranslation_add,show -χ+χ = 0 from neg_add_cancel χ,zeroMotiveTranslation_zero]
    rfl
  have hr (f : ZeroMotiveAlgebra) : zeroMotiveTranslation χ (zeroMotiveTranslation (-χ) f) = f := by
    change ((zeroMotiveTranslation χ).comp (zeroMotiveTranslation (-χ))) f = f
    rw [← zeroMotiveTranslation_add,show χ+(-χ) = 0 from add_neg_cancel χ,zeroMotiveTranslation_zero]
    rfl
  constructor
  · intro f g h
    exact (hl f).symm.trans ((congrArg (zeroMotiveTranslation (-χ)) h).trans (hl g))
  · intro f
    exact ⟨zeroMotiveTranslation (-χ) f,hr f⟩

/-- The algebraic centralizer consists exactly of translations by arbitrary complex motive points. -/
theorem primeTranslation_algebra_centralizer (F : ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra) :
    CommutesWithPrimeTranslations F.toLinearMap ↔
      ∃! χ : RawZeroMotivePoint, F = zeroMotiveTranslation χ := by
  constructor
  · intro h
    obtain ⟨c,hc,_⟩ := (primeTranslation_linear_centralizer F.toLinearMap).mp h
    let χ : RawZeroMotivePoint := zeroMotivePointEquiv.symm ((zeroMotiveEvaluation 0).comp F)
    have hχ : (fun z => ((χ z).toMul : ℂ)) = c := by
      funext z
      change zeroMotiveEvaluation 0 (F (AddMonoidAlgebra.single z 1)) = c z
      have he := congrArg (fun L : ZeroMotiveAlgebra →ₗ[ℂ] ZeroMotiveAlgebra =>
        L (AddMonoidAlgebra.single z 1)) hc
      change F (AddMonoidAlgebra.single z 1) = _ at he
      rw [zeroMotiveDiagonal_single,mul_one] at he
      rw [he,zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one]
    have he : F = zeroMotiveTranslation χ := by
      apply AlgHom.ext
      intro f
      have hl : F.toLinearMap = (zeroMotiveTranslation χ).toLinearMap := by
        rw [zeroMotiveTranslation_diagonal,hχ]
        exact hc
      exact DFunLike.congr_fun hl f
    refine ⟨χ,he,?_⟩
    intro ψ hψ
    exact zeroMotiveTranslation_injective (hψ.symm.trans he)
  · rintro ⟨χ,rfl,_⟩
    rw [zeroMotiveTranslation_diagonal]
    exact zeroMotiveDiagonal_commutes _

/-- Every algebra endomorphism commuting with the two prime translations is automatically invertible. -/
theorem primeTranslation_commuting_endomorphism_bijective
    (F : ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra)
    (h : CommutesWithPrimeTranslations F.toLinearMap) : Function.Bijective F := by
  obtain ⟨χ,rfl,_⟩ := (primeTranslation_algebra_centralizer F).mp h
  exact zeroMotiveTranslation_bijective χ

/-- Fixing the identity point removes the entire translation centralizer. -/
theorem primeTranslation_pointed_centralizer (F : ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra) :
    (CommutesWithPrimeTranslations F.toLinearMap ∧
      (zeroMotiveEvaluation 0).comp F = zeroMotiveEvaluation 0) ↔
      F = AlgHom.id ℂ ZeroMotiveAlgebra := by
  constructor
  · rintro ⟨h,hε⟩
    obtain ⟨χ,rfl,_⟩ := (primeTranslation_algebra_centralizer F).mp h
    have hz : χ = 0 := by
      apply AddMonoidHom.ext
      intro z
      apply Additive.toMul.injective
      apply Units.ext
      have he := congrArg (fun e : ZeroMotiveAlgebra →ₐ[ℂ] ℂ =>
        e (AddMonoidAlgebra.single z 1)) hε
      simp only [AlgHom.comp_apply,zeroMotiveTranslation_single,zeroMotiveEvaluation_single,
        zero_mul,Complex.exp_zero,mul_one,one_mul] at he
      exact he
    rw [hz,zeroMotiveTranslation_zero]
  · rintro rfl
    exact ⟨⟨fun _ => rfl,fun _ => rfl⟩,rfl⟩


/-- An ideal is stable when translating by either prime point preserves it. -/
def PrimeTranslationStable (J : Ideal ZeroMotiveAlgebra) : Prop :=
  ∀ f ∈ J, zeroMotivePrimeTranslation 2 f ∈ J ∧ zeroMotivePrimeTranslation 3 f ∈ J

/-- Two prime translations make the full zero-motive algebra difference-simple. -/
theorem primeTranslation_stable_ideal_iff (J : Ideal ZeroMotiveAlgebra) :
    PrimeTranslationStable J ↔ J = ⊥ ∨ J = ⊤ := by
  classical
  constructor
  · intro hJ
    by_cases hbot : J = ⊥
    · exact Or.inl hbot
    right
    have hex₀ : ∃ f : ZeroMotiveAlgebra, f ∈ J ∧ f ≠ 0 := by
      by_contra! h
      apply hbot
      apply le_antisymm ?_ bot_le
      intro f hf
      change f = 0
      exact h f hf
    have hex : ∃ n : ℕ, ∃ f : ZeroMotiveAlgebra,
        f ∈ J ∧ f ≠ 0 ∧ f.coeff.support.card = n := by
      obtain ⟨f,hf,hf₀⟩ := hex₀
      exact ⟨f.coeff.support.card,f,hf,hf₀,rfl⟩
    obtain ⟨f,hf,hf₀,hcard⟩ := Nat.find_spec hex
    have hmin (g : ZeroMotiveAlgebra) (hg : g ∈ J) (hg₀ : g ≠ 0) :
        f.coeff.support.card ≤ g.coeff.support.card := by
      rw [hcard]
      exact Nat.find_min' hex ⟨g,hg,hg₀,rfl⟩
    have hcoeff₀ : f.coeff ≠ 0 := by
      intro h
      exact hf₀ (AddMonoidAlgebra.coeff_injective h)
    obtain ⟨z,hz⟩ := Finsupp.support_nonempty_iff.mpr hcoeff₀
    have hsingle : ∀ w ∈ f.coeff.support, w = z := by
      intro w hw
      by_contra hwz
      have hdiff : zeroPrimeEigenvalue 2 w ≠ zeroPrimeEigenvalue 2 z ∨
          zeroPrimeEigenvalue 3 w ≠ zeroPrimeEigenvalue 3 z := by
        by_contra! h
        exact hwz (zeroPrimeEigenvalue_pair_injective (Prod.ext h.1 h.2))
      obtain ⟨p,hp,hsep⟩ : ∃ p : ℕ, (p = 2 ∨ p = 3) ∧
          zeroPrimeEigenvalue p w ≠ zeroPrimeEigenvalue p z := by
        rcases hdiff with h | h
        · exact ⟨2,Or.inl rfl,h⟩
        · exact ⟨3,Or.inr rfl,h⟩
      let g := zeroMotivePrimeTranslation p f-zeroPrimeEigenvalue p z • f
      have hg : g ∈ J := by
        apply J.sub_mem
        · rcases hp with rfl | rfl
          · exact (hJ f hf).1
          · exact (hJ f hf).2
        · rw [Algebra.smul_def]
          exact J.mul_mem_left _ hf
      have hgc (v : rawZeroRelationGroup) :
          g.coeff v = (zeroPrimeEigenvalue p v-zeroPrimeEigenvalue p z)*f.coeff v := by
        change (zeroMotivePrimeTranslation p f).coeff v-zeroPrimeEigenvalue p z*f.coeff v = _
        rw [zeroMotivePrimeTranslation_coeff]
        ring
      have hg₀ : g ≠ 0 := by
        intro h
        have he := congrArg (fun a : ZeroMotiveAlgebra => a.coeff w) h
        rw [hgc] at he
        exact (mul_ne_zero (sub_ne_zero.mpr hsep) (Finsupp.mem_support_iff.mp hw)) he
      have hsupport : g.coeff.support ⊆ f.coeff.support.erase z := by
        intro v hv
        have hgv := Finsupp.mem_support_iff.mp hv
        apply Finset.mem_erase.mpr
        constructor
        · intro he
          subst v
          exact hgv (by rw [hgc,sub_self,zero_mul])
        · by_contra hn
          exact hgv (by rw [hgc,Finsupp.notMem_support_iff.mp hn,mul_zero])
      have hlt : g.coeff.support.card < f.coeff.support.card :=
        lt_of_le_of_lt (Finset.card_le_card hsupport) (Finset.card_erase_lt_of_mem hz)
      exact (not_lt_of_ge (hmin g hg hg₀)) hlt
    have he : f = AddMonoidAlgebra.single z (f.coeff z) := by
      apply AddMonoidAlgebra.coeff_injective
      apply Finsupp.ext
      intro w
      by_cases hwz : w = z
      · subst w
        simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_eq_same]
      · have hw : w ∉ f.coeff.support := fun hw => hwz (hsingle w hw)
        simp only [Finsupp.notMem_support_iff.mp hw,AddMonoidAlgebra.coeff_single,
          Finsupp.single_eq_of_ne hwz]
    have hu : AddMonoidAlgebra.single (-z) ((f.coeff z)⁻¹)*f = 1 := by
      calc
        AddMonoidAlgebra.single (-z) ((f.coeff z)⁻¹)*f =
            AddMonoidAlgebra.single (-z) ((f.coeff z)⁻¹)*
              AddMonoidAlgebra.single z (f.coeff z) := congrArg
          (fun a => AddMonoidAlgebra.single (-z) ((f.coeff z)⁻¹)*a) he
        _ = 1 := by
          rw [AddMonoidAlgebra.single_mul_single,neg_add_cancel,
            inv_mul_cancel₀ (Finsupp.mem_support_iff.mp hz)]
          rfl
    have hone : (1 : ZeroMotiveAlgebra) ∈ J := hu ▸ J.mul_mem_left _ hf
    apply top_unique
    intro a _
    simpa only [mul_one] using J.mul_mem_left a hone
  · rintro (rfl | rfl)
    · intro f hf
      have he : f = 0 := hf
      subst f
      simp only [map_zero,Submodule.zero_mem,and_self]
    · intro f _
      exact ⟨trivial,trivial⟩

/-- Evaluating after translation is evaluation at the product of the two motive points. -/
theorem zeroMotiveCharacterEvaluation_translation (χ ψ : RawZeroMotivePoint) :
    (zeroMotiveCharacterEvaluation χ).comp (zeroMotiveTranslation ψ) =
      zeroMotiveCharacterEvaluation (χ+ψ) := by
  apply (AddMonoidAlgebra.lift ℂ ℂ rawZeroRelationGroup).symm.injective
  apply MonoidHom.ext
  intro z
  change zeroMotiveCharacterEvaluation χ
    (zeroMotiveTranslation ψ (AddMonoidAlgebra.single z.toAdd 1)) =
      zeroMotiveCharacterEvaluation (χ+ψ) (AddMonoidAlgebra.single z.toAdd 1)
  rw [zeroMotiveTranslation_single,zeroMotiveCharacterEvaluation_single,
    zeroMotiveCharacterEvaluation_single,one_mul,one_mul]
  change ((ψ z.toAdd).toMul : ℂ)*((χ z.toAdd).toMul : ℂ) =
    ((χ z.toAdd).toMul : ℂ)*((ψ z.toAdd).toMul : ℂ)
  exact mul_comm _ _

/-- The nonnegative two-prime orbit through an arbitrary complex motive point. -/
def zeroMotivePrimeOrbitPoint (χ : RawZeroMotivePoint) (k : ℕ × ℕ) : RawZeroMotivePoint :=
  χ+k.1 • rawZeroMotiveFlow (Real.log 2)+k.2 • rawZeroMotiveFlow (Real.log 3)

/-- Simultaneous evaluation on the entire two-prime orbit. -/
def zeroMotivePrimeOrbitEvaluation (χ : RawZeroMotivePoint) :
    ZeroMotiveAlgebra →ₐ[ℂ] ((ℕ × ℕ) → ℂ) :=
  AlgHom.pi fun k => zeroMotiveCharacterEvaluation (zeroMotivePrimeOrbitPoint χ k)

private theorem zeroMotivePrimeOrbitEvaluation_two (χ : RawZeroMotivePoint)
    (f : ZeroMotiveAlgebra) (m n : ℕ) :
    zeroMotivePrimeOrbitEvaluation χ (zeroMotivePrimeTranslation 2 f) (m,n) =
      zeroMotivePrimeOrbitEvaluation χ f (m+1,n) := by
  change ((zeroMotiveCharacterEvaluation (zeroMotivePrimeOrbitPoint χ (m,n))).comp
    (zeroMotiveTranslation (rawZeroMotiveFlow (Real.log 2)))) f = _
  rw [zeroMotiveCharacterEvaluation_translation]
  apply congrArg (fun η => zeroMotiveCharacterEvaluation η f)
  dsimp [zeroMotivePrimeOrbitPoint]
  rw [add_nsmul (rawZeroMotiveFlow (Real.log 2)) m 1,
    one_nsmul (rawZeroMotiveFlow (Real.log 2))]
  abel

private theorem zeroMotivePrimeOrbitEvaluation_three (χ : RawZeroMotivePoint)
    (f : ZeroMotiveAlgebra) (m n : ℕ) :
    zeroMotivePrimeOrbitEvaluation χ (zeroMotivePrimeTranslation 3 f) (m,n) =
      zeroMotivePrimeOrbitEvaluation χ f (m,n+1) := by
  change ((zeroMotiveCharacterEvaluation (zeroMotivePrimeOrbitPoint χ (m,n))).comp
    (zeroMotiveTranslation (rawZeroMotiveFlow (Real.log 3)))) f = _
  rw [zeroMotiveCharacterEvaluation_translation]
  apply congrArg (fun η => zeroMotiveCharacterEvaluation η f)
  dsimp [zeroMotivePrimeOrbitPoint]
  rw [add_nsmul (rawZeroMotiveFlow (Real.log 3)) n 1,
    one_nsmul (rawZeroMotiveFlow (Real.log 3))]
  abel

/-- Every nonnegative two-prime orbit is Zariski dense in the full zero motive. -/
theorem zeroMotivePrimeOrbitEvaluation_injective (χ : RawZeroMotivePoint) :
    Function.Injective (zeroMotivePrimeOrbitEvaluation χ) := by
  let J : Ideal ZeroMotiveAlgebra := RingHom.ker (zeroMotivePrimeOrbitEvaluation χ).toRingHom
  have hstable : PrimeTranslationStable J := by
    intro f hf
    change zeroMotivePrimeOrbitEvaluation χ f = 0 at hf
    constructor
    · change zeroMotivePrimeOrbitEvaluation χ (zeroMotivePrimeTranslation 2 f) = 0
      funext k
      rw [zeroMotivePrimeOrbitEvaluation_two]
      exact congrFun hf (k.1+1,k.2)
    · change zeroMotivePrimeOrbitEvaluation χ (zeroMotivePrimeTranslation 3 f) = 0
      funext k
      rw [zeroMotivePrimeOrbitEvaluation_three]
      exact congrFun hf (k.1,k.2+1)
  have hproper : J ≠ ⊤ := by
    intro h
    have hmem : (1 : ZeroMotiveAlgebra) ∈ J := by rw [h]; trivial
    have he : zeroMotivePrimeOrbitEvaluation χ 1 = 0 := hmem
    have hc := congrFun he (0,0)
    exact one_ne_zero (by simpa only [map_one,Pi.one_apply,Pi.zero_apply] using hc)
  have hbot := ((primeTranslation_stable_ideal_iff J).mp hstable).resolve_right hproper
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hmem : f ∈ J := hf
  rw [hbot] at hmem
  exact hmem

/-- At the identity, the orbit consists exactly of the two-prime power times. -/
theorem zeroMotivePrimeOrbitPoint_zero (m n : ℕ) :
    zeroMotivePrimeOrbitPoint 0 (m,n) =
      rawZeroMotiveFlow ((m : ℝ)*Real.log 2+(n : ℝ)*Real.log 3) := by
  have hm : rawZeroMotiveFlow ((m : ℝ)*Real.log 2) = m • rawZeroMotiveFlow (Real.log 2) := by
    simpa only [nsmul_eq_mul] using map_nsmul rawZeroMotiveFlow m (Real.log 2)
  have hn : rawZeroMotiveFlow ((n : ℝ)*Real.log 3) = n • rawZeroMotiveFlow (Real.log 3) := by
    simpa only [nsmul_eq_mul] using map_nsmul rawZeroMotiveFlow n (Real.log 3)
  change (0 : RawZeroMotivePoint)+m • rawZeroMotiveFlow (Real.log 2)+
    n • rawZeroMotiveFlow (Real.log 3) = _
  rw [zero_add (m • rawZeroMotiveFlow (Real.log 2)),
    map_add rawZeroMotiveFlow _ _,hm,hn]

/-- Values at the times `log(2^m 3^n)` determine every regular function without a height cutoff. -/
theorem zeroMotive_eq_iff_twoPrimePower_values (f g : ZeroMotiveAlgebra) :
    f = g ↔ ∀ m n : ℕ,
      zeroMotiveEvaluation (((m : ℝ)*Real.log 2+(n : ℝ)*Real.log 3 : ℝ) : ℂ) f =
      zeroMotiveEvaluation (((m : ℝ)*Real.log 2+(n : ℝ)*Real.log 3 : ℝ) : ℂ) g := by
  constructor
  · rintro rfl m n
    rfl
  · intro h
    apply zeroMotivePrimeOrbitEvaluation_injective 0
    funext k
    change zeroMotiveCharacterEvaluation (zeroMotivePrimeOrbitPoint 0 k) f =
      zeroMotiveCharacterEvaluation (zeroMotivePrimeOrbitPoint 0 k) g
    rw [show k = (k.1,k.2) from rfl,zeroMotivePrimeOrbitPoint_zero]
    have he := zeroMotivePointEquiv_flow ((k.1 : ℝ)*Real.log 2+(k.2 : ℝ)*Real.log 3)
    change zeroMotiveCharacterEvaluation _ = zeroMotiveEvaluation _ at he
    rw [he]
    exact h k.1 k.2

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveTranslation_diagonal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.exponent_eq_zero_of_two_prime_periods
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.two_prime_exponential_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotive_joint_eigenvector
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_linear_centralizer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_algebra_centralizer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_commuting_endomorphism_bijective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_pointed_centralizer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_stable_ideal_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotivePrimeOrbitEvaluation_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotive_eq_iff_twoPrimePower_values
