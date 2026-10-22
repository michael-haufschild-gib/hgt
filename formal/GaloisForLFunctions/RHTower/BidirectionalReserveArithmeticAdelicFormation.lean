import GaloisForLFunctions.HTGeometry.BidirectionalReserveFormation
import GaloisForLFunctions.RHTower.CCM.CCMRationalIntegralAdeleHaarIndex
import GaloisForLFunctions.RHTower.Sieve.TwistedMainTermMerge
import Mathlib

open Set
open scoped Pointwise

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

local notation "IntegralAdeles" => ccmRationalIntegralFiniteAdelesAddSubgroup

/-!
# Arithmetic and adelic realization of bidirectional reserve formation

Positive arithmetic histories split uniquely into a primitive observer and a diagonal gcd reserve.
Componentwise multiplication creates a cross-gcd reserve whose square pays the exact reduced-product
defect. Bounded unreduced activity is proper although the primitive observer has an unbounded
diagonal fibre. The gauge/reflection-selected half-density is simultaneously the critical reduced-
ray coefficient and the square root of the actual finite-adele lattice-mass ratio.
-/

/-- Primitive observer after removing common arithmetic reserve. -/
def arithmeticPrimitiveObserver (a b : ℕ) : ℕ × ℕ :=
  (a / Nat.gcd a b, b / Nat.gcd a b)

/-- Common diagonal reserve of an arithmetic bidirectional history. -/
def arithmeticReserve (a b : ℕ) : ℕ := Nat.gcd a b

/-- Multiplicative activity of an arithmetic bidirectional history. -/
def arithmeticActivity (a b : ℕ) : ℕ := a * b

/-- Componentwise multiplicative fusion of two arithmetic histories. -/
def arithmeticFusion (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.1, x.2 * y.2)

/-- New common reserve created by arithmetic fusion. -/
def arithmeticReserveTransgression (a b c d : ℕ) : ℕ :=
  Nat.gcd (a * c) (b * d) / (Nat.gcd a b * Nat.gcd c d)

theorem arithmeticPrimitiveObserver_activity_reconstruction (a b : ℕ) :
    (arithmeticPrimitiveObserver a b).1 *
        (arithmeticPrimitiveObserver a b).2 * arithmeticReserve a b ^ 2 =
      arithmeticActivity a b := by
  exact RHTower.Sieve.reducedProduct_mul_gcd_sq a b

/-- Removing the full common reserve leaves a primitive coprime observer. -/
theorem arithmeticPrimitiveObserver_coprime {a b : ℕ} (ha : 0 < a) :
    Nat.Coprime (arithmeticPrimitiveObserver a b).1
      (arithmeticPrimitiveObserver a b).2 := by
  simpa [arithmeticPrimitiveObserver] using
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left b ha)

/-- The coprime primitive observer and diagonal reserve factorization are unique. -/
theorem arithmeticPrimitiveObserver_reserve_unique
    {a b h a₀ b₀ : ℕ} (ha : 0 < a)
    (hab : a = h * a₀) (hbb : b = h * b₀) (hc : Nat.Coprime a₀ b₀) :
    h = arithmeticReserve a b ∧ (a₀, b₀) = arithmeticPrimitiveObserver a b := by
  have hh : 0 < h := by
    have hne : h ≠ 0 := by
      intro hz
      subst h
      simp at hab
      omega
    exact Nat.pos_of_ne_zero hne
  have hgcd : Nat.gcd a b = h := by
    rw [hab, hbb, Nat.gcd_mul_left, hc.gcd_eq_one, mul_one]
  constructor
  · simpa [arithmeticReserve] using hgcd.symm
  · change (a₀, b₀) = (a / Nat.gcd a b, b / Nat.gcd a b)
    rw [hgcd, hab, hbb, Nat.mul_div_cancel_left _ hh,
      Nat.mul_div_cancel_left _ hh]

/-- Additive logarithmic form of primitive/reserve activity reconstruction. -/
theorem arithmeticActivity_log_reconstruction
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (arithmeticActivity a b : ℝ) =
      Real.log (((arithmeticPrimitiveObserver a b).1 *
        (arithmeticPrimitiveObserver a b).2 : ℕ) : ℝ) +
        2 * Real.log (arithmeticReserve a b : ℝ) := by
  have hg : 0 < arithmeticReserve a b := Nat.gcd_pos_of_pos_left b ha
  have hp₁ : 0 < (arithmeticPrimitiveObserver a b).1 := by
    simp only [arithmeticPrimitiveObserver]
    exact Nat.div_pos (Nat.gcd_le_left b ha) (Nat.gcd_pos_of_pos_left b ha)
  have hp₂ : 0 < (arithmeticPrimitiveObserver a b).2 := by
    simp only [arithmeticPrimitiveObserver]
    exact Nat.div_pos (Nat.gcd_le_right a hb) (Nat.gcd_pos_of_pos_right a hb)
  have hrecon := arithmeticPrimitiveObserver_activity_reconstruction a b
  have hreconR :
      ((((arithmeticPrimitiveObserver a b).1 *
        (arithmeticPrimitiveObserver a b).2) * arithmeticReserve a b ^ 2 : ℕ) : ℝ) =
        (arithmeticActivity a b : ℝ) := by
    exact_mod_cast hrecon
  rw [← hreconR, Nat.cast_mul, Real.log_mul]
  · rw [Nat.cast_pow, Real.log_pow]
    norm_num
  · positivity
  · positivity

theorem arithmeticReserve_product_dvd_fusedReserve (a b c d : ℕ) :
    Nat.gcd a b * Nat.gcd c d ∣ Nat.gcd (a * c) (b * d) := by
  apply Nat.dvd_gcd
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_left c d)
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_right c d)

theorem arithmeticReserveTransgression_mul_oldReserve (a b c d : ℕ) :
    arithmeticReserveTransgression a b c d *
        (Nat.gcd a b * Nat.gcd c d) =
      Nat.gcd (a * c) (b * d) := by
  exact Nat.div_mul_cancel (arithmeticReserve_product_dvd_fusedReserve a b c d)

theorem arithmeticPrimitiveObserver_fusion_conservation (a b c d : ℕ) :
    ((arithmeticPrimitiveObserver a b).1 * (arithmeticPrimitiveObserver a b).2) *
        ((arithmeticPrimitiveObserver c d).1 * (arithmeticPrimitiveObserver c d).2) =
      ((arithmeticPrimitiveObserver (a * c) (b * d)).1 *
          (arithmeticPrimitiveObserver (a * c) (b * d)).2) *
        arithmeticReserveTransgression a b c d ^ 2 := by
  let g₁ := Nat.gcd a b
  let g₂ := Nat.gcd c d
  let g₃ := Nat.gcd (a * c) (b * d)
  let P₁ := (arithmeticPrimitiveObserver a b).1 * (arithmeticPrimitiveObserver a b).2
  let P₂ := (arithmeticPrimitiveObserver c d).1 * (arithmeticPrimitiveObserver c d).2
  let P₃ := (arithmeticPrimitiveObserver (a * c) (b * d)).1 *
    (arithmeticPrimitiveObserver (a * c) (b * d)).2
  let K := arithmeticReserveTransgression a b c d
  have h₁ : P₁ * g₁ ^ 2 = a * b := arithmeticPrimitiveObserver_activity_reconstruction a b
  have h₂ : P₂ * g₂ ^ 2 = c * d := arithmeticPrimitiveObserver_activity_reconstruction c d
  have h₃ : P₃ * g₃ ^ 2 = (a * c) * (b * d) :=
    arithmeticPrimitiveObserver_activity_reconstruction (a * c) (b * d)
  have hK : K * (g₁ * g₂) = g₃ :=
    arithmeticReserveTransgression_mul_oldReserve a b c d
  by_cases hz : g₁ * g₂ = 0
  · have hg₁ : g₁ = 0 ∨ g₂ = 0 := Nat.mul_eq_zero.mp hz
    rcases hg₁ with hg₁ | hg₂
    · have hab : a = 0 ∧ b = 0 := Nat.gcd_eq_zero_iff.mp hg₁
      simp [arithmeticPrimitiveObserver, hab.1, hab.2]
    · have hcd : c = 0 ∧ d = 0 := Nat.gcd_eq_zero_iff.mp hg₂
      simp [arithmeticPrimitiveObserver, hcd.1, hcd.2]
  · apply Nat.mul_right_cancel (Nat.pos_of_ne_zero (pow_ne_zero 2 hz))
    calc
      (P₁ * P₂) * (g₁ * g₂) ^ 2 = (P₁ * g₁ ^ 2) * (P₂ * g₂ ^ 2) := by ring
      _ = (a * b) * (c * d) := by rw [h₁, h₂]
      _ = (a * c) * (b * d) := by ring
      _ = P₃ * g₃ ^ 2 := h₃.symm
      _ = (P₃ * K ^ 2) * (g₁ * g₂) ^ 2 := by rw [← hK]; ring

/-- The `p`-adic valuation of a positive gcd is the minimum of the two valuations. -/
theorem padicValNat_gcd_eq_min
    {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  have h := DFunLike.congr_fun (Nat.factorization_gcd ha hb) p
  simpa [Nat.factorization_def _ (Fact.out : p.Prime)] using h

/-- Primewise reserve birth is the minimum transgression of valuation channels. -/
theorem padicValNat_arithmeticReserveTransgression
    {p a b c d : ℕ} [Fact p.Prime]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    padicValNat p (arithmeticReserveTransgression a b c d) =
      min (padicValNat p a + padicValNat p c)
          (padicValNat p b + padicValNat p d) -
        (min (padicValNat p a) (padicValNat p b) +
          min (padicValNat p c) (padicValNat p d)) := by
  rw [arithmeticReserveTransgression,
    padicValNat.div_of_dvd (arithmeticReserve_product_dvd_fusedReserve a b c d),
    padicValNat_gcd_eq_min (mul_ne_zero ha.ne' hc.ne') (mul_ne_zero hb.ne' hd.ne'),
    padicValNat.mul ha.ne' hc.ne', padicValNat.mul hb.ne' hd.ne',
    padicValNat.mul (Nat.gcd_pos_of_pos_left b ha).ne'
      (Nat.gcd_pos_of_pos_left d hc).ne',
    padicValNat_gcd_eq_min ha.ne' hb.ne', padicValNat_gcd_eq_min hc.ne' hd.ne']

/-- Literal ordered-group form: every prime valuation of arithmetic reserve birth is the
bidirectional reserve transgression. -/
theorem padicValNat_arithmeticReserveTransgression_eq_transgression
    {p a b c d : ℕ} [Fact p.Prime]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (padicValNat p (arithmeticReserveTransgression a b c d) : ℤ) =
      BidirectionalFormation.transgression
        ((padicValNat p a : ℤ), (padicValNat p b : ℤ))
        ((padicValNat p c : ℤ), (padicValNat p d : ℤ)) := by
  let first := min (padicValNat p a + padicValNat p c)
    (padicValNat p b + padicValNat p d)
  let second := min (padicValNat p a) (padicValNat p b) +
    min (padicValNat p c) (padicValNat p d)
  have hnat : padicValNat p (arithmeticReserveTransgression a b c d) =
      first - second := padicValNat_arithmeticReserveTransgression ha hb hc hd
  have hle : second ≤ first := min_add_min_le_min_add_add
  have hcast : (padicValNat p (arithmeticReserveTransgression a b c d) : ℤ) =
      (first : ℤ) - second := by
    rw [← Nat.cast_sub hle]
    exact_mod_cast hnat
  rw [hcast]
  simp only [first, second, Nat.cast_add, Nat.cast_min,
    BidirectionalFormation.transgression, BidirectionalFormation.reserve,
    Prod.fst_add, Prod.snd_add]
  abel

/-- Concrete additive coordinates on the integral finite adeles. -/
noncomputable def ccmRationalIntegralFiniteAdelesPadicEquiv :
    IntegralAdeles ≃+ ((p : Nat.Primes) → ℤ_[p]) :=
  ccmRationalIntegralPiAddEquivIntegralFiniteAdeles.symm.trans
    ccmRationalIntegralPiPadicEquiv

/-- Multiplication by a nonzero natural is injective on the integral finite adeles. -/
theorem ccmRationalIntegralFiniteAdeles_nsmul_injective
    {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun x : IntegralAdeles => n • x) := by
  intro x y h
  apply ccmRationalIntegralFiniteAdelesPadicEquiv.injective
  have hm := congrArg ccmRationalIntegralFiniteAdelesPadicEquiv h
  have hinj : Function.Injective
      (fun z : ((p : Nat.Primes) → ℤ_[p]) => n • z) :=
    nsmul_right_injective hn
  exact hinj (by simpa using hm)

private theorem exists_lcm_nsmul
    {a b : ℕ} (ha : 0 < a) {x : IntegralAdeles}
    (hax : x ∈ (nsmulAddMonoidHom (α := IntegralAdeles) a).range)
    (hbx : x ∈ (nsmulAddMonoidHom (α := IntegralAdeles) b).range) :
    ∃ w : IntegralAdeles, Nat.lcm a b • w = x := by
  obtain ⟨y, hy⟩ := hax
  obtain ⟨z, hz⟩ := hbx
  let g := Nat.gcd a b
  let a₀ := a / g
  let b₀ := b / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : g * a₀ = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * b₀ = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hc : Nat.Coprime a₀ b₀ := Nat.coprime_div_gcd_div_gcd hg
  have hred : a₀ • y = b₀ • z := by
    apply ccmRationalIntegralFiniteAdeles_nsmul_injective hg.ne'
    simpa [nsmulAddMonoidHom, ← mul_nsmul, Nat.mul_comm, hga, hgb] using
      hy.trans hz.symm
  let w : IntegralAdeles := Nat.gcdA a₀ b₀ • z + Nat.gcdB a₀ b₀ • y
  have hbez : (1 : ℤ) =
      (a₀ : ℤ) * Nat.gcdA a₀ b₀ + (b₀ : ℤ) * Nat.gcdB a₀ b₀ := by
    simpa [hc.gcd_eq_one] using Nat.gcd_eq_gcd_ab a₀ b₀
  have hyw : b₀ • w = y := by
    have hredZ : (a₀ : ℤ) • y = (b₀ : ℤ) • z := by simpa using hred
    change (b₀ : ℤ) • w = y
    calc
      (b₀ : ℤ) • w = Nat.gcdA a₀ b₀ • ((b₀ : ℤ) • z) +
          Nat.gcdB a₀ b₀ • ((b₀ : ℤ) • y) := by
        dsimp [w]
        module
      _ = Nat.gcdA a₀ b₀ • ((a₀ : ℤ) • y) +
          Nat.gcdB a₀ b₀ • ((b₀ : ℤ) • y) := by rw [← hredZ]
      _ = ((a₀ : ℤ) * Nat.gcdA a₀ b₀ +
          (b₀ : ℤ) * Nat.gcdB a₀ b₀) • y := by module
      _ = y := by rw [← hbez]; simp
  have hlcm : Nat.lcm a b = g * (a₀ * b₀) := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
      _ = (g * a₀) * (g * b₀) := by rw [hga, hgb]
      _ = g * (g * (a₀ * b₀)) := by ring
  refine ⟨w, ?_⟩
  rw [← hy]
  change Nat.lcm a b • w = a • y
  rw [← hyw, hlcm, ← hga]
  simp only [mul_nsmul]
  module

private theorem lcm_nsmul_range_eq_inf
    {a b : ℕ} (ha : 0 < a) :
    (nsmulAddMonoidHom (α := IntegralAdeles) (Nat.lcm a b)).range =
      (nsmulAddMonoidHom (α := IntegralAdeles) a).range ⊓
        (nsmulAddMonoidHom (α := IntegralAdeles) b).range := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · obtain ⟨k, hk⟩ := Nat.dvd_lcm_left a b
      exact ⟨k • w, by simp [nsmulAddMonoidHom, ← mul_nsmul, hk, Nat.mul_comm]⟩
    · obtain ⟨k, hk⟩ := Nat.dvd_lcm_right a b
      exact ⟨k • w, by simp [nsmulAddMonoidHom, ← mul_nsmul, hk, Nat.mul_comm]⟩
  · rintro ⟨hax, hbx⟩
    obtain ⟨w, hw⟩ := exists_lcm_nsmul ha hax hbx
    exact ⟨w, by simpa [nsmulAddMonoidHom] using hw⟩

/-- Actual integral finite-adele lattices intersect by least common multiple. -/
theorem ccmRationalIntegralFiniteAdelesNSMulSet_lcm_eq_inter
    {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    ccmRationalIntegralFiniteAdelesNSMulSet (Nat.lcm a b) =
      ccmRationalIntegralFiniteAdelesNSMulSet a ∩
        ccmRationalIntegralFiniteAdelesNSMulSet b := by
  rw [← ccmRationalIntegralFiniteAdelesSubtype_image_nsmulRange,
    ← ccmRationalIntegralFiniteAdelesSubtype_image_nsmulRange,
    ← ccmRationalIntegralFiniteAdelesSubtype_image_nsmulRange,
    lcm_nsmul_range_eq_inf ha]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  · rintro ⟨⟨y, hy, hyx⟩, ⟨z, hz, hzx⟩⟩
    have hyz : y = z := Subtype.val_injective (hyx.trans hzx.symm)
    subst z
    exact ⟨y, ⟨hy, hz⟩, hyx⟩

/-- Actual integral finite-adele lattices add by greatest common divisor. -/
theorem ccmRationalIntegralFiniteAdelesNSMulSet_add_eq_gcd (a b : ℕ) :
    ccmRationalIntegralFiniteAdelesNSMulSet a +
        ccmRationalIntegralFiniteAdelesNSMulSet b =
      ccmRationalIntegralFiniteAdelesNSMulSet (Nat.gcd a b) := by
  ext x
  constructor
  · rintro ⟨u, ⟨y, rfl⟩, v, ⟨z, rfl⟩, rfl⟩
    obtain ⟨a₀, ha₀⟩ := Nat.gcd_dvd_left a b
    obtain ⟨b₀, hb₀⟩ := Nat.gcd_dvd_right a b
    refine ⟨a₀ • y + b₀ • z, ?_⟩
    change Nat.gcd a b • ((a₀ • y + b₀ • z).1 : CCMRationalFiniteAdele) =
      a • (y.1 : CCMRationalFiniteAdele) + b • (z.1 : CCMRationalFiniteAdele)
    have haZ : (a : ℤ) = (Nat.gcd a b : ℤ) * (a₀ : ℤ) := by exact_mod_cast ha₀
    have hbZ : (b : ℤ) = (Nat.gcd a b : ℤ) * (b₀ : ℤ) := by exact_mod_cast hb₀
    change (Nat.gcd a b : ℤ) •
        ((a₀ : ℤ) • (y.1 : CCMRationalFiniteAdele) +
          (b₀ : ℤ) • (z.1 : CCMRationalFiniteAdele)) =
      (a : ℤ) • (y.1 : CCMRationalFiniteAdele) +
        (b : ℤ) • (z.1 : CCMRationalFiniteAdele)
    rw [haZ, hbZ]
    module
  · rintro ⟨z, rfl⟩
    let za : IntegralAdeles := Nat.gcdA a b • z
    let zb : IntegralAdeles := Nat.gcdB a b • z
    refine ⟨a • (za.1 : CCMRationalFiniteAdele), ⟨za, rfl⟩,
      b • (zb.1 : CCMRationalFiniteAdele), ⟨zb, rfl⟩, ?_⟩
    have hbez := Nat.gcd_eq_gcd_ab a b
    change a • (za.1 : CCMRationalFiniteAdele) +
      b • (zb.1 : CCMRationalFiniteAdele) =
        Nat.gcd a b • (z.1 : CCMRationalFiniteAdele)
    dsimp [za, zb]
    change (a : ℤ) • (Nat.gcdA a b • (z.1 : CCMRationalFiniteAdele)) +
      (b : ℤ) • (Nat.gcdB a b • (z.1 : CCMRationalFiniteAdele)) =
        (Nat.gcd a b : ℤ) • (z.1 : CCMRationalFiniteAdele)
    rw [hbez]
    module

/-- Bounded multiplicative activity has finite unreduced arithmetic sublevels. -/
theorem finite_arithmeticFormationSublevel (B : ℕ) :
    {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧ arithmeticActivity x.1 x.2 ≤ B}.Finite := by
  apply (Set.finite_Icc (1, 1) (B, B)).subset
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  have haB : a ≤ B := by
    have haab : a ≤ a * b := by
      simpa using Nat.mul_le_mul_left a (show 1 ≤ b by omega)
    exact haab.trans hab
  have hbB : b ≤ B := by
    have hbab : b ≤ a * b := by
      simpa [mul_comm] using Nat.mul_le_mul_left b (show 1 ≤ a by omega)
    exact hbab.trans hab
  exact ⟨⟨by omega, by omega⟩, ⟨haB, hbB⟩⟩

theorem arithmeticPrimitiveObserver_diagonal {k : ℕ} (hk : 0 < k) :
    arithmeticPrimitiveObserver k k = (1, 1) := by
  simp [arithmeticPrimitiveObserver, Nat.gcd_self, Nat.div_self hk]

theorem arithmeticActivity_diagonal (k : ℕ) : arithmeticActivity k k = k ^ 2 := by
  simp [arithmeticActivity, pow_two]

/-- One observer fibre has unbounded unreduced activity. -/
theorem arithmeticPrimitiveObserver_notProper :
    ∀ B : ℕ, ∃ k : ℕ,
      arithmeticPrimitiveObserver k k = (1, 1) ∧ B < arithmeticActivity k k := by
  intro B
  refine ⟨B + 1, arithmeticPrimitiveObserver_diagonal (by omega), ?_⟩
  rw [arithmeticActivity_diagonal]
  have hle : B + 1 ≤ (B + 1) ^ 2 := by
    rw [pow_two]
    simpa only [mul_one] using
      Nat.mul_le_mul_left (B + 1) (show 1 ≤ B + 1 by omega)
  omega

theorem arithmeticFusion_reflected_closes (a : ℕ) :
    arithmeticFusion (a, 1) (1, a) = (a, a) := by
  simp [arithmeticFusion]

/-- Gauge/reflection-selected arithmetic half-density. -/
def arithmeticHalfDensity (a b : ℕ) : ℝ :=
  (Nat.gcd a b : ℝ) / Real.sqrt ((a : ℝ) * (b : ℝ))

theorem arithmeticHalfDensity_eq_inv_sqrt_primitiveProduct
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    arithmeticHalfDensity a b =
      (Real.sqrt (((arithmeticPrimitiveObserver a b).1 *
        (arithmeticPrimitiveObserver a b).2 : ℕ) : ℝ))⁻¹ := by
  exact (RHTower.Sieve.inv_sqrt_reducedProduct ha hb).symm

/-- Real-valued normalized Haar mass of the actual lattice `n Zhat`. -/
def integralAdeleLatticeMassReal (n : ℕ) : ℝ :=
  (ccmRationalFiniteAdeleHaar (ccmRationalIntegralFiniteAdelesNSMulSet n)).toReal

theorem integralAdeleLatticeMassReal_eq_inv {n : ℕ} (hn : n ≠ 0) :
    integralAdeleLatticeMassReal n = (n : ℝ)⁻¹ := by
  rw [integralAdeleLatticeMassReal,
    ccmRationalFiniteAdeleHaar_integralSubring_nsmul hn,
    ENNReal.toReal_inv]
  simp

theorem integralAdeleLatticeMassRatio_gcd_lcm
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    integralAdeleLatticeMassReal (Nat.lcm a b) /
        integralAdeleLatticeMassReal (Nat.gcd a b) =
      (Nat.gcd a b : ℝ) / (Nat.lcm a b : ℝ) := by
  have hg : Nat.gcd a b ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left b ha)
  have hl : Nat.lcm a b ≠ 0 := Nat.ne_of_gt (Nat.lcm_pos ha hb)
  rw [integralAdeleLatticeMassReal_eq_inv hl,
    integralAdeleLatticeMassReal_eq_inv hg]
  field_simp

theorem arithmeticHalfDensity_sq_eq_adelicMassRatio
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    arithmeticHalfDensity a b ^ 2 =
      integralAdeleLatticeMassReal (Nat.lcm a b) /
        integralAdeleLatticeMassReal (Nat.gcd a b) := by
  rw [integralAdeleLatticeMassRatio_gcd_lcm ha hb]
  have hab : (0 : ℝ) < (a : ℝ) * (b : ℝ) := by positivity
  have hg : (0 : ℝ) < (Nat.gcd a b : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left b ha
  have hl : (0 : ℝ) < (Nat.lcm a b : ℝ) := by
    exact_mod_cast (Nat.lcm_pos ha hb)
  have hgl : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  rw [arithmeticHalfDensity, div_pow, Real.sq_sqrt hab.le]
  field_simp [ne_of_gt hab, ne_of_gt hg, ne_of_gt hl]
  nlinarith

/-- The selected half-density is exactly the square root of the actual adelic lattice interval. -/
theorem arithmeticHalfDensity_eq_sqrt_adelicMassRatio
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    arithmeticHalfDensity a b =
      Real.sqrt
        (integralAdeleLatticeMassReal (Nat.lcm a b) /
          integralAdeleLatticeMassReal (Nat.gcd a b)) := by
  rw [← arithmeticHalfDensity_sq_eq_adelicMassRatio ha hb,
    Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg]
  exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- Closed certificate joining reserve conservation, arithmetic fusion/properness, forced
half-density, actual finite-adele Haar mass, and the critical reduced-ray coefficient. -/
theorem bidirectionalReserveArithmeticAdelicFormation_certificate :
    (∀ x y : BidirectionalFormation ℝ,
      BidirectionalFormation.visible x + BidirectionalFormation.visible y =
        BidirectionalFormation.visible (x + y) +
          (2 : ℕ) • BidirectionalFormation.transgression x y) ∧
    (∀ α β : ℝ,
      ((∀ r x y t, formationLogPotential α β (r + t) (x + t) (y + t) =
          formationLogPotential α β r x y) ∧
        (∀ r x y, formationLogPotential α β r y x =
          formationLogPotential α β r x y)) ↔
        α = 1 / 2 ∧ β = 1 / 2) ∧
    (∀ a b : ℕ,
      (arithmeticPrimitiveObserver a b).1 *
          (arithmeticPrimitiveObserver a b).2 * arithmeticReserve a b ^ 2 =
        arithmeticActivity a b) ∧
    (∀ a b c d : ℕ,
      ((arithmeticPrimitiveObserver a b).1 * (arithmeticPrimitiveObserver a b).2) *
          ((arithmeticPrimitiveObserver c d).1 * (arithmeticPrimitiveObserver c d).2) =
        ((arithmeticPrimitiveObserver (a * c) (b * d)).1 *
            (arithmeticPrimitiveObserver (a * c) (b * d)).2) *
          arithmeticReserveTransgression a b c d ^ 2) ∧
    (∀ B : ℕ,
      {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧ arithmeticActivity x.1 x.2 ≤ B}.Finite) ∧
    (∀ B : ℕ, ∃ k : ℕ,
      arithmeticPrimitiveObserver k k = (1, 1) ∧ B < arithmeticActivity k k) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      arithmeticHalfDensity a b =
          (Real.sqrt (((arithmeticPrimitiveObserver a b).1 *
            (arithmeticPrimitiveObserver a b).2 : ℕ) : ℝ))⁻¹ ∧
        arithmeticHalfDensity a b =
          Real.sqrt
            (integralAdeleLatticeMassReal (Nat.lcm a b) /
              integralAdeleLatticeMassReal (Nat.gcd a b))) := by
  exact ⟨BidirectionalFormation.visible_fusion_conservation,
    formationLogPotential_gauge_reflection_unique,
    arithmeticPrimitiveObserver_activity_reconstruction,
    arithmeticPrimitiveObserver_fusion_conservation,
    finite_arithmeticFormationSublevel,
    arithmeticPrimitiveObserver_notProper,
    fun _ _ ha hb =>
      ⟨arithmeticHalfDensity_eq_inv_sqrt_primitiveProduct ha hb,
        arithmeticHalfDensity_eq_sqrt_adelicMassRatio ha hb⟩⟩

/-- Zero-argument certificate for every structural, arithmetic, valuation, and actual-lattice law
used by bidirectional reserve formation. All domain restrictions are quantified internally. -/
theorem bidirectionalReserveArithmeticAdelicFormation_completion_certificate :
    (∀ x : BidirectionalFormation ℝ,
      BidirectionalFormation.activity x = BidirectionalFormation.visible x +
        (2 : ℕ) • BidirectionalFormation.reserve x) ∧
    (∀ x y : BidirectionalFormation ℝ,
      0 ≤ BidirectionalFormation.transgression x y) ∧
    (∀ x y z : BidirectionalFormation ℝ,
      BidirectionalFormation.transgression x y +
          BidirectionalFormation.transgression (x + y) z =
        BidirectionalFormation.transgression y z +
          BidirectionalFormation.transgression x (y + z)) ∧
    (∀ x y : BidirectionalFormation ℝ,
      BidirectionalFormation.transgression
          (BidirectionalFormation.reflect x) (BidirectionalFormation.reflect y) =
        BidirectionalFormation.transgression x y) ∧
    (∀ x y : BidirectionalFormation ℝ,
      0 ≤ BidirectionalFormation.current x →
      0 ≤ BidirectionalFormation.current y →
      BidirectionalFormation.transgression x y = 0) ∧
    (∀ x y : BidirectionalFormation ℝ,
      BidirectionalFormation.current x ≤ 0 →
      BidirectionalFormation.current y ≤ 0 →
      BidirectionalFormation.transgression x y = 0) ∧
    (∀ x y : BidirectionalFormation ℝ,
      0 ≤ BidirectionalFormation.current x →
      BidirectionalFormation.current y ≤ 0 →
      BidirectionalFormation.transgression x y =
        min (BidirectionalFormation.visible x) (BidirectionalFormation.visible y)) ∧
    (∀ x y : BidirectionalFormation ℝ,
      BidirectionalFormation.current x ≤ 0 →
      0 ≤ BidirectionalFormation.current y →
      BidirectionalFormation.transgression x y =
        min (BidirectionalFormation.visible x) (BidirectionalFormation.visible y)) ∧
    (∀ x y : ℝ,
      Real.exp (formationLogPotential (1 / 2) (1 / 2) (min x y) x y) =
        Real.exp (-|x - y| / 2)) ∧
    (∀ a b : ℕ, 0 < a →
      Nat.Coprime (arithmeticPrimitiveObserver a b).1
        (arithmeticPrimitiveObserver a b).2) ∧
    (∀ a b h a₀ b₀ : ℕ,
      0 < a → a = h * a₀ → b = h * b₀ → Nat.Coprime a₀ b₀ →
      h = arithmeticReserve a b ∧
        (a₀, b₀) = arithmeticPrimitiveObserver a b) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      Real.log (arithmeticActivity a b : ℝ) =
        Real.log (((arithmeticPrimitiveObserver a b).1 *
          (arithmeticPrimitiveObserver a b).2 : ℕ) : ℝ) +
          2 * Real.log (arithmeticReserve a b : ℝ)) ∧
    (∀ (p : Nat.Primes) (a b c d : ℕ),
      0 < a → 0 < b → 0 < c → 0 < d →
      (padicValNat p.1 (arithmeticReserveTransgression a b c d) : ℤ) =
        BidirectionalFormation.transgression
          ((padicValNat p.1 a : ℤ), (padicValNat p.1 b : ℤ))
          ((padicValNat p.1 c : ℤ), (padicValNat p.1 d : ℤ))) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      ccmRationalIntegralFiniteAdelesNSMulSet (Nat.lcm a b) =
        ccmRationalIntegralFiniteAdelesNSMulSet a ∩
          ccmRationalIntegralFiniteAdelesNSMulSet b) ∧
    (∀ a b : ℕ,
      ccmRationalIntegralFiniteAdelesNSMulSet a +
          ccmRationalIntegralFiniteAdelesNSMulSet b =
        ccmRationalIntegralFiniteAdelesNSMulSet (Nat.gcd a b)) := by
  exact ⟨BidirectionalFormation.activity_eq_visible_add_two_reserve,
    BidirectionalFormation.transgression_nonneg,
    BidirectionalFormation.transgression_cocycle,
    BidirectionalFormation.transgression_reflect,
    BidirectionalFormation.transgression_eq_zero_of_currents_nonneg,
    BidirectionalFormation.transgression_eq_zero_of_currents_nonpos,
    BidirectionalFormation.transgression_eq_min_visible_of_current_nonneg_nonpos,
    BidirectionalFormation.transgression_eq_min_visible_of_current_nonpos_nonneg,
    criticalFormationExpPotential_eq_exp_neg_visible_half,
    fun _ _ ha => arithmeticPrimitiveObserver_coprime ha,
    fun _ _ _ _ _ ha hab hbb hc =>
      arithmeticPrimitiveObserver_reserve_unique ha hab hbb hc,
    fun _ _ ha hb => arithmeticActivity_log_reconstruction ha hb,
    fun _ _ _ _ _ ha hb hc hd =>
      padicValNat_arithmeticReserveTransgression_eq_transgression ha hb hc hd,
    fun _ _ ha hb =>
      ccmRationalIntegralFiniteAdelesNSMulSet_lcm_eq_inter ha hb,
    ccmRationalIntegralFiniteAdelesNSMulSet_add_eq_gcd⟩

end

end GaloisForLFunctions.RHTower
