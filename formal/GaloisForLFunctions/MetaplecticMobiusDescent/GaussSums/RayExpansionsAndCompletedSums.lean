/-
Ray expansions and completed Gauss sums adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.CompletedHeightTwists
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.SecondPassNormalizedMass

/-!
# Ray expansions and completed Gauss sums

Fourier expansion on unit residue classes modulo four (`RayFourExpansion`, `FiniteRayExpansion`)
with coefficient mass at most one. Angular, column and cube weights of the completed Gauss sum
and the completed cusp array `completedCuspArray`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

def unitFourierCoeff (f : Rˣ → ℂ) (χ : MulChar R ℂ) : ℂ :=
  (∑ u : Rˣ, f u * star (χ (u : R))) / (Fintype.card Rˣ : ℂ)

theorem unit_fourier_inversion (f : Rˣ → ℂ) (v : Rˣ) :
    (∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ (v : R)) = f v := by
  have hN : (Fintype.card Rˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [unitFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteRingSieve.unit_char_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_div_cancel_right₀ (f v) hN

theorem norm_char_unit (χ : MulChar R ℂ) (u : Rˣ) : ‖χ (u : R)‖ = 1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem norm_char_le_one (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (norm_char_unit χ u).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem unitFourierCoeff_norm_le_average (f : Rˣ → ℂ) (χ : MulChar R ℂ) :
    ‖unitFourierCoeff f χ‖ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := by
  rw [unitFourierCoeff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ u : Rˣ, ‖f u * star (χ (u : R))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_star, norm_char_unit, mul_one]

theorem unitFourierCoeff_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) (χ : MulChar R ℂ) : ‖unitFourierCoeff f χ‖ ≤ B := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := unitFourierCoeff_norm_le_average f χ
    _ ≤ (∑ _u : Rˣ, B) / (Fintype.card Rˣ : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hf u)) (by positivity)
    _ = B := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem character_card_eq_units : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ

theorem unitFourierCoeff_sum_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ (Fintype.card Rˣ : ℝ) * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le f B hf χ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]

theorem unitFourierCoeff_sum_norm_le_sum (f : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ ∑ u : Rˣ, ‖f u‖ := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le_average f χ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      field_simp

def zeroExtendUnits (f : Rˣ → ℂ) (r : R) : ℂ :=
  if hr : IsUnit r then f hr.unit else 0

@[simp] theorem zeroExtendUnits_unit (f : Rˣ → ℂ) (u : Rˣ) :
    zeroExtendUnits f (u : R) = f u := by
  rw [zeroExtendUnits, dif_pos u.isUnit]
  congr 1
  exact Units.ext u.isUnit.unit_spec

@[simp] theorem zeroExtendUnits_nonunit (f : Rˣ → ℂ) (r : R) (hr : ¬ IsUnit r) :
    zeroExtendUnits f r = 0 := dif_neg hr

theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

theorem zeroExtendUnits_restrict (f : R → ℂ) (r : R) :
    zeroExtendUnits (fun u : Rˣ => f (u : R)) r = (if IsUnit r then 1 else 0) * f r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnits_unit, u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]


end FiniteRayExpansion

namespace RayFourExpansion
open Eisenstein SchwartzPlanePoisson FiniteRayExpansion
open scoped Classical
abbrev RayRing := QuadraticRayRing
abbrev RayCharacter := MulChar RayRing ℂ
noncomputable instance rayCharacterFintype : Fintype RayCharacter := Fintype.ofFinite _

def rayMonoid (χ : RayCharacter) : O →* ℂ :=
  χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {(4 : O)})).toMonoidHom

@[simp] theorem rayMonoid_apply (χ : RayCharacter) (a : O) :
    rayMonoid χ a = χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) := rfl

theorem rayMonoid_norm_le (χ : RayCharacter) (a : O) : ‖rayMonoid χ a‖ ≤ 1 :=
  norm_char_le_one χ _

def phaseCoeff (f : RayRing → ℂ) (χ : RayCharacter) : ℂ :=
  unitFourierCoeff (fun u : RayRingˣ => f (u : RayRing)) χ

/-- Fourier expansion on the unit residue classes modulo four. -/
theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    (if IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) then 1 else 0) *
        f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayMonoid χ a := by
  rw [← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

theorem phaseCoeff_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) (χ : RayCharacter) :
    ‖phaseCoeff f χ‖ ≤ B := unitFourierCoeff_norm_le _ B hf χ

theorem phaseCoeff_sum_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ‖phaseCoeff f χ‖) ≤ (Fintype.card RayRingˣ : ℝ) * B :=
  unitFourierCoeff_sum_norm_le _ B hf

end RayFourExpansion

namespace RayFourExpansion
open Eisenstein SchwartzPlanePoisson
open scoped Classical

theorem prime_unit_mod_four (p : O) [(Ideal.span {p}).IsMaximal]
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) p) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have h2 : (2 : O) ∉ Ideal.span {p} := by
    intro hm
    have hz : (2 : O ⧸ Ideal.span {p}) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
    apply hchar
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ Ideal.span {p}) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ Ideal.span {p}) 2).mp hz)
  let : (Ideal.span {(2 : O)}).IsMaximal := by
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  have hcop : IsCoprime (Ideal.span {p}) (Ideal.span {(2 : O)}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    apply h2
    rw [heq]
    exact Ideal.subset_span (by simp)
  have hcp : IsCoprime p (2 : O) := (Ideal.isCoprime_span_singleton_iff _ _).mp hcop
  have hcp4 : IsCoprime p (4 : O) := by
    simpa only [show (2 : O) ^ 2 = 4 by norm_num] using
      (hcp.pow_right : IsCoprime p ((2 : O) ^ 2))
  obtain ⟨a, b, hab⟩ := hcp4
  have hz : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (4 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {(4 : O)})) hab
  simp only [map_add, map_mul, map_one, hz, mul_zero, add_zero] at hm
  exact IsUnit.of_mul_eq_one_right _ hm

theorem prime_product_unit_mod_four {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i)) := by
  rw [map_prod]
  exact IsUnit.prod_iff.mpr (fun i _ => prime_unit_mod_four (p i) (hchar i))


end RayFourExpansion

namespace RayFourExpansion
open Eisenstein SchwartzPlanePoisson FiniteRayExpansion
open scoped Classical

def residueCoeff (r : RayRing) : RayCharacter → ℂ :=
  phaseCoeff (fun a=>if a=r then 1 else 0)

theorem residue_expansion (r : RayRing) (a : O)
    (ha : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)) :
    (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) a=r then (1 : ℂ) else 0) =
      ∑χ : RayCharacter,residueCoeff r χ*rayMonoid χ a := by
  simpa only [if_pos ha,one_mul,residueCoeff] using
    phase_expansion (fun x=>if x=r then 1 else 0) a

/-- A residue projection has Fourier coefficients of total absolute mass at most one. -/
theorem residueCoeff_sum_norm_le_one (r : RayRing) :
    (∑χ : RayCharacter,‖residueCoeff r χ‖) ≤ 1 := by
  apply (unitFourierCoeff_sum_norm_le_sum (fun u : RayRingˣ=>if (u : RayRing)=r then 1 else 0)).trans
  by_cases hr : IsUnit r
  · obtain ⟨u,rfl⟩:=hr
    have hi (v : RayRingˣ) : ((v : RayRing)=(u : RayRing)) ↔ v=u := Units.val_injective.eq_iff
    simp only [hi]
    simp_rw [show ∀x : RayRingˣ, ‖(if x=u then (1:ℂ) else 0)‖ =
        (if x=u then (1:ℝ) else 0) by intro x; split_ifs <;> simp]
    simp
  · have hn (u : RayRingˣ) : (u : RayRing)≠r := fun he=>hr (he ▸ u.isUnit)
    simp only [if_neg (hn _),norm_zero,Finset.sum_const_zero,zero_le_one]

end RayFourExpansion

open scoped Classical
open scoped Classical SchwartzMap

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

/-- Compact radial support bounds all three ideal norms in a cube convolution. -/
theorem compact_window_bound (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ y, W y ≠ 0 → y  ≤  B := by
  obtain ⟨B, hB⟩ := hW.bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact (hB (subset_tsupport W hy)).trans (le_max_left _ _)

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ)  ≤  Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_scale_bounds (a b c : ℝ) (ha : 1  ≤  a) (hb : 1  ≤  b) (hc : 1  ≤  c) :
    a  ≤  a * b ^ 3 * c ^ 3 ∧ b  ≤  a * b ^ 3 * c ^ 3 ∧ c  ≤  a * b ^ 3 * c ^ 3 := by
  have ha0 : 0  ≤  a := by linarith
  have hb0 : 0  ≤  b := by linarith
  have hc0 : 0  ≤  c := by linarith
  have hb3 : 1  ≤  b ^ 3 := one_le_pow₀ hb
  have hc3 : 1  ≤  c ^ 3 := one_le_pow₀ hc
  constructor
  · calc a = a * 1 * 1 := by ring
         _  ≤  a * b ^ 3 * c ^ 3 := by gcongr
  constructor
  · calc b  ≤  b ^ 3 := le_self_pow₀ hb (by decide)
         _ = 1 * b ^ 3 * 1 := by ring
         _  ≤  a * b ^ 3 * c ^ 3 := by gcongr
  · calc c  ≤  c ^ 3 := le_self_pow₀ hc (by decide)
         _ = 1 * 1 * c ^ 3 := by ring
         _  ≤  a * b ^ 3 * c ^ 3 := by gcongr

theorem finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * X)
  let S := {I : Ideal O | Ideal.absNorm I  ≤  M}
  have hS : S.Finite := Ideal.finite_setOf_absNorm_le (S := O) M
  apply (hS.prod (hS.prod hS)).subset
  rintro ⟨I, J, H⟩ hF
  have hF0 : F (I, J, H) ≠ 0 := hF
  have hI : I ≠ 0 := fun h => hF0 (hzero I J H (Or.inl h))
  have hJ : J ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inl h)))
  have hH : H ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inr h)))
  have hw : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
      (Ideal.absNorm H : ℝ) ^ 3 / X) ≠ 0 := fun h => hF0 (hwindow I J H h)
  have hsize := (div_le_iff₀ hX).mp (hbound _ hw)
  have hb := triple_scale_bounds _ _ _ (norm_at_least_one I hI)
    (norm_at_least_one J hJ) (norm_at_least_one H hH)
  have hIM : Ideal.absNorm I  ≤  M := by exact_mod_cast (hb.1.trans hsize).trans hM.le
  have hJM : Ideal.absNorm J  ≤  M := by exact_mod_cast (hb.2.1.trans hsize).trans hM.le
  have hHM : Ideal.absNorm H  ≤  M := by exact_mod_cast (hb.2.2.trans hsize).trans hM.le
  exact ⟨hIM, hJM, hHM⟩

theorem ideal_cube_convolution (c : Ideal O →* ℂ) (hc0 : c 0 = 0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2))).Finite) :
    (∑' H : Ideal O, ∑' J : Ideal O,
      (UniqueFactorizationMonoid.moebius H : ℂ) * c (H * J) * f (H * J)) = f 1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2)
  have hF : Summable F := summable_of_hasFiniteSupport hfinite
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      if B = 1 then f 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have heach : ∀ p : MulFiber 0, F p.val = 0 := by
        intro p
        dsimp [F]
        rw [p.property, hc0, mul_zero, zero_mul]
      simp only [heach, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = ∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) * (c B * f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property, mul_assoc]
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) * (c B * f B) := by
          rw [tsum_mul_right]
        _ = if B = 1 then f 1 else 0 := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with h
          · subst B; simp only [map_one, one_mul]
          · simp
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) (∑' p, F p) at hs
  simp_rw [hfiber] at hs
  have hsum : (∑' p, F p) = f 1 := by
    have he := hs.tsum_eq.symm
    simpa only [tsum_ite_eq, one_ne_zero] using he
  rw [← hF.tsum_prod]
  exact hsum

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

/-- The complex direction of an Eisenstein integer, zero at the origin. -/
def angularFactor (x : O) : ℂ := ringComplex x/(‖ringComplex x‖:ℂ)

lemma norm_angularFactor (x : O) (hx : x≠0) : ‖angularFactor x‖=1 := by
  rw [angularFactor,norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hx))]

lemma star_angularFactor (x : O) (hx : x≠0) :
    star (angularFactor x)=(‖ringComplex x‖:ℂ)/ringComplex x := by
  have hn : (‖ringComplex x‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hx))
  have he : star (ringComplex x)*ringComplex x=(‖ringComplex x‖:ℂ)^2 := by
    simpa only [Complex.star_def,Complex.ofReal_pow] using Complex.conj_mul' (ringComplex x)
  apply (eq_div_iff (ringComplex_ne_zero hx)).mpr
  rw [angularFactor,star_div₀,show star (‖ringComplex x‖:ℂ)=(‖ringComplex x‖:ℂ) by
    simp only [Complex.star_def,Complex.conj_ofReal],div_mul_eq_mul_div,he,pow_two]
  exact mul_div_cancel_right₀ _ hn

/-- Squarefree cubic Gauss coefficient with its primary angular phase. -/
def squarefreeGaussCoefficient (I : Ideal O) : ℂ :=
  if Squarefree I then star (angularFactor (primaryIdealGenerator I))*
    normalizedCubicUnitGauss (primaryIdealGenerator I) else 0

@[simp] theorem squarefreeGaussCoefficient_zero : squarefreeGaussCoefficient 0=0 := by
  simp only [squarefreeGaussCoefficient,primaryIdealGenerator_zero,angularFactor,
    map_zero,norm_zero,Complex.ofReal_zero,div_zero,star_zero,zero_mul,ite_self]

@[simp] theorem squarefreeGaussCoefficient_bot : squarefreeGaussCoefficient ⊥=0 :=
  squarefreeGaussCoefficient_zero

lemma squarefreeGaussCoefficient_of_primary_zero (I : Ideal O)
    (hI : primaryIdealGenerator I=0) : squarefreeGaussCoefficient I=0 := by
  simp only [squarefreeGaussCoefficient,hI,angularFactor,map_zero,norm_zero,
    Complex.ofReal_zero,div_zero,star_zero,zero_mul,ite_self]

theorem angularFactor_mul (a b : O) :
    angularFactor (a * b) =
      angularFactor a * angularFactor b := by
  simp only [angularFactor, map_mul, norm_mul, Complex.ofReal_mul]
  ring

def cubeWeight (Ψ : O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (angularFactor (primaryIdealGenerator I)) ^ 3 *
    Ψ (primaryIdealGenerator I) ^ 3 / (Ideal.absNorm I : ℂ)
  map_one' := by
    simp only [primaryIdealGenerator_one, angularFactor, map_one,
      norm_one, Complex.ofReal_one, div_one, star_one, one_pow, one_mul, Nat.cast_one]
  map_mul' I J := by
    simp only [primaryIdealGenerator_mul, angularFactor_mul, map_mul, star_mul, mul_pow, Nat.cast_mul]
    ring

@[simp] theorem cubeWeight_zero (Ψ : O →* ℂ) : cubeWeight Ψ 0 = 0 := by
  simp [cubeWeight, angularFactor]

@[simp] theorem cubeWeight_bot (Ψ : O →* ℂ) : cubeWeight Ψ ⊥ = 0 := cubeWeight_zero Ψ

def columnWeight (Ψ : O →* ℂ) (I : Ideal O) : ℂ :=
  squarefreeGaussCoefficient I * Ψ (primaryIdealGenerator I)

@[simp] theorem columnWeight_zero (Ψ : O →* ℂ) : columnWeight Ψ 0 = 0 := by
  simp [columnWeight]

@[simp] theorem columnWeight_bot (Ψ : O →* ℂ) : columnWeight Ψ ⊥ = 0 := columnWeight_zero Ψ

def summand (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) * cubeWeight Ψ J *
    Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)

def completedIdealT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, summand Ψ W X I J

theorem summand_zero_left (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (J : Ideal O) :
    summand Ψ W X 0 J = 0 := by simp [summand]

theorem summand_zero_right (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I : Ideal O) :
    summand Ψ W X I 0 = 0 := by simp [summand]

theorem summand_zero_window (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O)
    (h : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X) = 0) :
    summand Ψ W X I J = 0 := by simp [summand, Vstar, h]


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

def expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X))

theorem finite_support_expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O × Ideal O =>
      expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite := by
  apply finite_support_norm_triple W hW X hX
  · intro I H J hz
    rcases hz with rfl | rfl | rfl <;> simp [expandedTerm]
  · intro I H J hw
    simp [expandedTerm, Vstar, hw]

theorem expandedTerm_scale (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J = expandedTerm Ψ W X I H J := by
  have harg : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 /
      (X / (Ideal.absNorm H : ℝ) ^ 3) =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X := by
    rw [div_div_eq_mul_div]
    ring
  simp only [summand, expandedTerm, harg, map_mul]
  ring

theorem expandedTerm_one (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    expandedTerm Ψ W X I 1 J = summand Ψ W X I J := by
  simp only [expandedTerm, summand, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    one_mul, map_one, Nat.cast_one, one_pow, mul_one]
  ring

theorem completedIdealT_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2)).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hinj : Function.Injective (fun p : Ideal O × Ideal O => (p.1, (1 : Ideal O), p.2)) := by
    intro a b hab
    exact Prod.ext (Prod.mk.inj hab).1 (Prod.mk.inj (Prod.mk.inj hab).2).2
  have hp := Set.Finite.preimage hinj.injOn hf
  change (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X p.1 1 p.2)).Finite at hp
  simpa only [expandedTerm_one] using hp

theorem completedIdealT_summable (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2) :=
  summable_of_hasFiniteSupport (completedIdealT_finite_support Ψ W hW X hX)

theorem weighted_completedIdealT_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (H : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedIdealT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) =
      ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
  simp only [completedIdealT, ← tsum_mul_left, expandedTerm_scale]

theorem cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        completedIdealT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3))).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, expandedTerm Ψ W X I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_completedIdealT_reopen]
  simp only [hzero, tsum_zero]

theorem cube_inner_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J) =
      columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        expandedTerm Ψ W X I H J := by
    simp only [f, expandedTerm, map_mul, Nat.cast_mul, mul_pow, mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I, p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O =>
        expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem completed_cube_inverse_vstar (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedIdealT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3)) =
    ∑' I : Ideal O, columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p => expandedTerm Ψ W X p.1 p.2.1 p.2.2
  have hF : Summable F := summable_of_hasFiniteSupport (finite_support_expandedTerm Ψ W hW X hX)
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O, ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      simp only [completedIdealT, ← tsum_mul_left, expandedTerm_scale]
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F p := e.tsum_eq F
    _ = ∑' I : Ideal O, ∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (cube_inner_inverse Ψ W hW X hX)

theorem vstar_source_normalization (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  by_cases hI : I = 0
  · subst I; simp
  have hN : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hsN : (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hsX : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hX).ne'
  rw [Vstar, Real.sqrt_div hN.le, Complex.ofReal_div]
  field_simp

theorem completed_cube_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal O, columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedIdealT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) := by
  rw [completed_cube_inverse_vstar Ψ W hW X hX, ← tsum_mul_left]
  apply tsum_congr
  intro I
  simpa only [mul_assoc] using (vstar_source_normalization Ψ W X hX I).symm

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

lemma primaryIdealGenerator_norm (I : Ideal O) (hI : primaryIdealGenerator I≠0) :
    ‖ringComplex (primaryIdealGenerator I)‖=Real.sqrt (Ideal.absNorm I:ℝ) := by
  rw [←primaryIdealGenerator_norm_sq I hI,Real.sqrt_sq (norm_nonneg _)]

lemma cubeWeight_eq (Ψ : O→*ℂ) (I : Ideal O) (hI : primaryIdealGenerator I≠0) :
    cubeWeight Ψ I= (‖ringComplex (primaryIdealGenerator I)‖:ℂ)*
      Ψ (primaryIdealGenerator I)^3/ringComplex (primaryIdealGenerator I)^3 := by
  have hn : (‖ringComplex (primaryIdealGenerator I)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hI))
  have hN : (Ideal.absNorm I:ℂ)=(‖ringComplex (primaryIdealGenerator I)‖:ℂ)^2 := by
    exact_mod_cast (primaryIdealGenerator_norm_sq I hI).symm
  change star (angularFactor (primaryIdealGenerator I))^3*Ψ (primaryIdealGenerator I)^3/_=_
  rw [star_angularFactor _ hI,hN]
  field_simp

lemma columnWeight_div_sqrt (Ψ : O→*ℂ) (I : Ideal O)
    (hs : Squarefree I) (hI : primaryIdealGenerator I≠0) :
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)=
      normalizedCubicUnitGauss (primaryIdealGenerator I)*Ψ (primaryIdealGenerator I)/
        ringComplex (primaryIdealGenerator I) := by
  have hn : (‖ringComplex (primaryIdealGenerator I)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hI))
  rw [columnWeight,squarefreeGaussCoefficient,if_pos hs,star_angularFactor _ hI,
    ←primaryIdealGenerator_norm I hI]
  field_simp

lemma completedMellinCoefficient_eq (Ψ : O→*ℂ) (p : ThetaPrimaryCubePair) :
    completedMellinCoefficient Ψ p=
      columnWeight Ψ p.1.val/(Real.sqrt (Ideal.absNorm p.1.val:ℝ):ℂ)*cubeWeight Ψ p.2.val := by
  rw [columnWeight_div_sqrt Ψ _ p.1.property.1 p.1.property.2,
    cubeWeight_eq Ψ _ p.2.property]
  simp only [completedMellinCoefficient,map_mul,map_pow]
  ring

lemma completedMellinLength_eq (p : ThetaPrimaryCubePair) :
    completedMellinLength p=(Ideal.absNorm p.1.val:ℝ)*(Ideal.absNorm p.2.val:ℝ)^3 := by
  rw [completedMellinLength,sourceCuspRadialLength,
    if_neg (mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property)),
    map_mul,map_pow,norm_mul,norm_pow,mul_pow,
    primaryIdealGenerator_norm_sq _ p.1.property.2]
  rw [←pow_mul,show (3:ℕ)*2=2*3 by decide,pow_mul,
    primaryIdealGenerator_norm_sq _ p.2.property]

lemma summand_primary_support (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Ideal O)
    (h : summand Ψ W X I J≠0) :
    (Squarefree I ∧ primaryIdealGenerator I≠0) ∧ primaryIdealGenerator J≠0 := by
  have hc : squarefreeGaussCoefficient I≠0 := by
    intro hz
    exact h (by simp only [summand,columnWeight,hz,zero_mul,zero_div])
  refine ⟨⟨?_,?_⟩,?_⟩
  · by_contra hn
    exact hc (by rw [squarefreeGaussCoefficient,if_neg hn])
  · intro hz
    exact hc (squarefreeGaussCoefficient_of_primary_zero I hz)
  · intro hz
    have hw : cubeWeight Ψ J=0 := by
      change star (angularFactor (primaryIdealGenerator J))^3*Ψ (primaryIdealGenerator J)^3/_=0
      simp only [hz,angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
        div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
    exact h (by simp only [summand,hw,mul_zero,zero_mul])


/-- The ideal-indexed cube expansion equals the native completed Gauss sum. -/
theorem completedIdealT_eq_completedT (Ψ : O→*ℂ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    completedIdealT Ψ W X=completedT Ψ W X := by
  let f : Ideal O×Ideal O→ℂ := fun q=>summand Ψ W X q.1 q.2
  let φ : ThetaPrimaryCubePair→Ideal O×Ideal O := fun p=>(p.1.val,p.2.val)
  have hφ : Function.Injective φ := by
    intro p q he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  have hsum : (∑'q,f q)=∑'p:ThetaPrimaryCubePair,f (φ p) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun p : Function.support (fun p:ThetaPrimaryCubePair=>f (φ p))=>φ p.val)
    · exact hφ.comp Subtype.val_injective
    · intro q hq
      have hs:=summand_primary_support Ψ W X q.1 q.2 hq
      let p : ThetaPrimaryCubePair := (⟨q.1,hs.1⟩,⟨q.2,hs.2⟩)
      exact ⟨⟨p,hq⟩,rfl⟩
    · intro p
      rfl
  rw [completedIdealT,←(completedIdealT_summable Ψ W hW X hX).tsum_prod]
  change (∑'q,f q)=_
  rw [hsum,completedT]
  apply tsum_congr
  intro p
  rw [completedMellinCoefficient_eq,completedMellinLength_eq]
  rfl

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

def largeCubeCoefficient (H₀ : ℝ) (B : Ideal O) : ℂ :=
  if B=⊥ then 0 else ∑ H∈idealDivisors B,
    if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0

theorem largeCubeCoefficient_zero (H₀ : ℝ) : largeCubeCoefficient H₀ ⊥=0 := by
  simp [largeCubeCoefficient]

theorem largeCubeCoefficient_norm_le (H₀ : ℝ) (B : Ideal O) :
    ‖largeCubeCoefficient H₀ B‖ ≤ (idealDivisors B).card := by
  by_cases hB : B=⊥
  · simp [hB,largeCubeCoefficient]
  · rw [largeCubeCoefficient,if_neg hB]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ H∈idealDivisors B,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
        · simp only [if_pos h]
          by_cases hsf : Squarefree H
          · simp [hsf.moebius_eq]
          · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsf]
        · simp [h]
      _ = _ := by simp

theorem largeCubeCoefficient_support (H₀ : ℝ) (B : Ideal O)
    (h : largeCubeCoefficient H₀ B ≠ 0) : B≠⊥ ∧ H₀ ≤ (Ideal.absNorm B : ℝ) := by
  have hB : B≠⊥ := fun hb => h (by simp [hb,largeCubeCoefficient])
  refine ⟨hB,?_⟩
  rw [largeCubeCoefficient,if_neg hB] at h
  obtain ⟨H,hH,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hlarge : H₀ ≤ (Ideal.absNorm H : ℝ) := by
    by_contra hn
    exact hterm (if_neg hn)
  have hdiv := (mem_idealDivisors hB).mp hH
  have hpos : 0 < Ideal.absNorm B := Nat.pos_iff_ne_zero.mpr (fun hn => hB (Ideal.absNorm_eq_zero_iff.mp hn))
  exact hlarge.trans (by exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hdiv))

theorem large_cube_convolution (H₀ : ℝ) (c : Ideal O →* ℂ) (hc0 : c 0=0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2))).Finite) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then
        (UniqueFactorizationMonoid.moebius H : ℂ)*c (H*J)*f (H*J) else 0) =
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*c B*f B := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.1 : ℝ) then
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2) else 0
  have hF : Summable F := summable_of_hasFiniteSupport (hfinite.subset (by
    intro p hp
    by_contra hn
    have he : (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2)=0 := not_ne_iff.mp hn
    exact hp (by dsimp [F];rw [he];simp)))
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.val)=largeCubeCoefficient H₀ B*c B*f B := by
    by_cases hB : B=0
    · subst B
      have hz : ∀ p : MulFiber 0,F p.val=0 := by
        intro p
        dsimp [F]
        rw [p.property,hc0]
        simp
      simp [hz,largeCubeCoefficient]
    · let e := mulFiberDivisorEquiv B hB
      have hsum : (∑' p : MulFiber B,
          if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0) =
          largeCubeCoefficient H₀ B := by
        calc
          _ = ∑' H : {H : Ideal O // H∈idealDivisors B},
              if H₀ ≤ (Ideal.absNorm H.val : ℝ) then (UniqueFactorizationMonoid.moebius H.val : ℂ) else 0 :=
            e.tsum_eq _
          _ = _ := by
            rw [tsum_fintype,largeCubeCoefficient,if_neg (show B≠⊥ from hB)]
            exact (Finset.sum_subtype (idealDivisors B) (fun H => Iff.rfl)
              (fun H => if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0)).symm
      calc
        _ = ∑' p : MulFiber B,
            (if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0)*(c B*f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property]
          split_ifs <;> ring
        _ = _ := by rw [tsum_mul_right,hsum];ring
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.val) (∑' p,F p) at hs
  simp_rw [hfiber] at hs
  rw [← hF.tsum_prod]
  exact hs.tsum_eq.symm

theorem large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=expandedTerm Ψ W X I H J := by
    simp only [f,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring

theorem large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        completedIdealT Ψ W (X/(Ideal.absNorm H : ℝ)^3) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then expandedTerm Ψ W X p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((finite_support_expandedTerm Ψ W hW X hX).subset (by
      intro p hp
      by_contra hn
      have he : expandedTerm Ψ W X p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [if_pos h,weighted_completedIdealT_reopen]
      · simp only [if_neg h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (large_cube_inner_reopen Ψ W hW X H₀ hX)

theorem completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        completedIdealT Ψ W (X/(Ideal.absNorm H : ℝ)^3) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedIdealT Ψ W (X/(Ideal.absNorm H : ℝ)^3)
  have hf := cube_inverse_finite_support Ψ W hW X hX
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [completed_cube_inverse Ψ W hW X hX,←large_cube_reopen Ψ W hW X H₀ hX]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

theorem large_cube_block_progress (H₀ B F : ℝ) (hB : 0 ≤ B) (hF : 1 ≤ F)
    (I : Ideal O) (hI : largeCubeCoefficient H₀ I ≠ 0) (hIB : (Ideal.absNorm I : ℝ) ≤ B) :
    H₀ ≤ B*F := by
  have hlarge := (largeCubeCoefficient_support H₀ I hI).2
  exact (hlarge.trans hIB).trans (le_mul_of_one_le_right hB hF)

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

def shortCompletedSum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  ∑' H : Ideal O, if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
      completedIdealT Ψ W (X/(Ideal.absNorm H:ℝ)^3) else 0

def shortCubeRange (H₀ : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOf_absNorm_le (S := O) ⌈H₀⌉₊).toFinset.filter
    (fun H=>H≠0 ∧ (Ideal.absNorm H:ℝ)<H₀)

theorem mem_shortCubeRange (H₀ : ℝ) (H : Ideal O) :
    H∈shortCubeRange H₀ ↔ H≠0 ∧ (Ideal.absNorm H:ℝ)<H₀ := by
  rw [shortCubeRange,Finset.mem_filter,Set.Finite.mem_toFinset]
  constructor
  · exact And.right
  · intro h
    exact ⟨Nat.cast_le.mp (h.2.le.trans (Nat.le_ceil H₀)),h⟩

theorem shortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) :
    shortCompletedSum Ψ W X H₀ = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        completedIdealT Ψ W (X/(Ideal.absNorm H:ℝ)^3) := by
  unfold shortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => if_pos ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact if_neg hn

theorem cube_inverse_weight_norm (Ψ : O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (H : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H‖≤1/(Ideal.absNorm H:ℝ) := by
  have hang : ‖angularFactor (primaryIdealGenerator H)‖≤1 := by
    by_cases hz : primaryIdealGenerator H=0
    · simp [hz,angularFactor]
    · exact (norm_angularFactor _ hz).le
  have hw : ‖cubeWeight Ψ H‖≤1/(Ideal.absNorm H:ℝ) := by
    change ‖star (angularFactor (primaryIdealGenerator H))^3*Ψ (primaryIdealGenerator H)^3/(Ideal.absNorm H:ℂ)‖≤_
    rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h1 : ‖angularFactor (primaryIdealGenerator H)‖^3≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hang 3
    have h2 : ‖Ψ (primaryIdealGenerator H)‖^3≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hΨ _) 3
    nlinarith [pow_nonneg (norm_nonneg (Ψ (primaryIdealGenerator H))) 3]
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one H)).trans hw


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic
open scoped Classical

theorem short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖completedIdealT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤A) :
    (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤
      A*(descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖shortCompletedSum (Ψ k) W X H₀‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedIdealT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
    rw [shortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖completedIdealT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedIdealT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖completedIdealT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ) :=
    descent_ideal_inverse_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped Classical

lemma largeCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀H₀:ℝ,∀B:Ideal O,B≠0 →
      ‖largeCubeCoefficient H₀ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=IdealDivisorBound.ideal_divisor_small_power ε hε
  exact ⟨C,hC,fun H₀ B hB=>(largeCubeCoefficient_norm_le H₀ B).trans (hbound B hB)⟩

theorem cubeWeight_norm_le (Ψ : O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖angularFactor (primaryIdealGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryIdealGenerator B=0
    · simp [hz,angularFactor]
    · exact (norm_angularFactor _ hz).le
  change ‖star (angularFactor (primaryIdealGenerator B))^3*
    Ψ (primaryIdealGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

def cubePhase (Ψ : O →* ℂ) (B : Ideal O) : ℂ :=
  (Ideal.absNorm B:ℂ)*cubeWeight Ψ B

theorem cubePhase_norm_le (Ψ : O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem cube_weight_scale (Ψ : O →* ℂ) (B : Ideal O) (hB : B≠0)
    (X : ℝ) (hX : 0<X) :
    cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹ =
      cubePhase Ψ B * (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)/(Real.sqrt X:ℂ) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hs3 : Real.sqrt ((Ideal.absNorm B:ℝ)^3) =
      (Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ) := by
    rw [show (Ideal.absNorm B:ℝ)^3=(Ideal.absNorm B:ℝ)^2*(Ideal.absNorm B:ℝ) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hN]
  have hs : Real.sqrt (X/(Ideal.absNorm B:ℝ)^3) =
      Real.sqrt X/((Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ)) := by
    rw [Real.sqrt_div hX.le,hs3]
  rw [hs,Complex.ofReal_div,Complex.ofReal_mul,cubePhase]
  push_cast
  have hNc : (Ideal.absNorm B:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hsN : (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsX : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  field_simp

def reopenedCubeCoefficient (H₀ : ℝ) (Ψ : O →* ℂ) (B : Ideal O) : ℂ :=
  largeCubeCoefficient H₀ B * cubePhase Ψ B

theorem reopenedCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀(H₀:ℝ) (Ψ:O →* ℂ), (∀z,‖Ψ z‖≤1) →
      ∀B:Ideal O,B≠0 → ‖reopenedCubeCoefficient H₀ Ψ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := largeCubeCoefficient_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro H₀ Ψ hΨ B hB
  rw [reopenedCubeCoefficient,norm_mul]
  calc
    _ ≤ ‖largeCubeCoefficient H₀ B‖*1 :=
      mul_le_mul_of_nonneg_left (cubePhase_norm_le Ψ hΨ B) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hbound H₀ B hB

theorem reopenedCubeCoefficient_support (H₀:ℝ) (Ψ:O →* ℂ) (B:Ideal O)
    (h:reopenedCubeCoefficient H₀ Ψ B≠0) : B≠0 ∧ H₀ ≤ (Ideal.absNorm B:ℝ) := by
  exact largeCubeCoefficient_support H₀ B (fun hz=>h (by simp only [reopenedCubeCoefficient,hz,zero_mul]))

end CompletedGauss

namespace CompletedGauss
open Eisenstein
open scoped Classical
lemma shortCompletedSum_nonpos (Ψ : O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (hH : H₀ ≤ 0) :
    shortCompletedSum Ψ W X H₀=0 := by
  calc
    _ = ∑' I : Ideal O,(0:ℂ) := by
      apply tsum_congr
      intro I
      exact if_neg (not_lt_of_ge (hH.trans (Nat.cast_nonneg (Ideal.absNorm I))))
    _ = 0 := tsum_zero
end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma prime_support_subsets_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀I:Ideal O,I≠0 → (2:ℝ)^(primeSupport I).card≤C*(Ideal.absNorm I:ℝ)^ε := by
  obtain ⟨C,hC,hb⟩:=IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro I hI
  have hc : 2^(primeSupport I).card≤(idealDivisors I).card := by
    have he : ((primeSupport I).powerset.image (fun S=>∏P∈S,P)).card=
        (primeSupport I).powerset.card := Finset.card_image_iff.mpr (by
      intro S hS T hT he
      exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) he)
    rw [←Finset.card_powerset,←he,←squarefree_divisors_eq_image I hI]
    exact Finset.card_filter_le _ _
  exact (show (2:ℝ)^(primeSupport I).card≤((idealDivisors I).card:ℝ) by exact_mod_cast hc).trans (hb I hI)

theorem completed_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(I : Ideal O),I≠0 → ∀{ι : Type*} [Fintype ι]
      (P : ι→Ideal O) [∀i,(P i).IsMaximal],Function.Injective P →
      (∀i,P i∣I) → (6:ℝ)^(2*Fintype.card ι)≤C*(Ideal.absNorm I:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := prime_support_subsets_bound (ε/6) (by positivity)
  refine ⟨C ^ 6,by positivity,?_⟩
  intro I hI ι _ P _ hinj hd
  let f : ι→primeSupport I := fun i => ⟨P i,by
    change P i∈(normalizedFactors I).toFinset
    exact Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr
      ⟨Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance,hd i⟩)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card ι≤(primeSupport I).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfi
  have htwo : (2:ℝ)^Fintype.card ι≤C*(Ideal.absNorm I:ℝ)^(ε/6) :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard).trans (hbound I hI)
  have hn : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  calc
    _ = (36:ℝ)^Fintype.card ι := by rw [pow_mul]; norm_num
    _ ≤ (64:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^6 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm I:ℝ)^(ε/6))^6 := pow_le_pow_left₀ (by positivity) htwo 6
    _ = C ^ 6*(Ideal.absNorm I:ℝ)^ε := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      congr 2
      ring

end CompletedGauss

namespace CompletedGauss
open scoped BigOperators Classical
open MeasureTheory

theorem finite_tsum_energy_bound {κ α : Type*} [Fintype κ]
    (f : α→κ→ℂ) (g : α→ℝ) (hg0 : ∀i,0≤g i) (hg : Summable g)
    (hbound : ∀i,(∑k,‖f i k‖^2)≤(g i)^2) :
    (∀k,Summable (fun i => ‖f i k‖)) ∧
    (∑k,‖∑'i,f i k‖^2)≤(∑'i,g i)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : α→EuclideanSpace ℂ κ := fun i => e.symm (f i)
  have hF (i : α) : ‖F i‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    rw [EuclideanSpace.norm_sq_eq]
    exact hbound i
  have hpoint (k : κ) (i : α) : ‖f i k‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖f i j‖) (Finset.mem_univ k)).trans
      (hbound i)
  have hsum (k : κ) : Summable (fun i => ‖f i k‖) :=
    hg.of_nonneg_of_le (fun i => norm_nonneg _) (hpoint k)
  have hfp : Summable f := Pi.summable.mpr (fun k => (hsum k).of_norm)
  have he : (∑'i,F i)=e.symm (fun k => ∑'i,f i k) := by
    rw [show (fun i => F i)=(fun i => e.symm (f i)) from rfl,←e.symm.map_tsum]
    congr 1
    funext k
    exact tsum_apply hfp
  have hn : ‖e.symm (fun k => ∑'i,f i k)‖≤∑'i,g i := by
    rw [←he]
    exact tsum_of_norm_bounded hg.hasSum hF
  refine ⟨hsum,?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq] at hs
  exact hs


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Fourier separation of the completed radial kernel, uniform in the positive scale. -/
theorem completed_kernel_log_separation
    {ι : Type*} [Fintype ι] (V : ι→ℝ→ℂ) (slope M : ι→ℝ)
    (hM : ∀i,0≤M i) (hV : ∀i y,V i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*paperKernel (Vstar W)
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*kernelLogPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) volume ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_log_separation V slope M hM hV (Vstar W) a b ha
    (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) A J
  exact ⟨C,hC.le,by simpa only [Real.norm_eq_abs] using hb⟩

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

lemma ramified_unit_norm (u : Oˣ) (m : ℕ) :
    ‖ringComplex ((u:O)*lambda^m)‖=(3:ℝ)^((m:ℝ)/2) := by
  have hl : ‖ringComplex lambda‖=Real.sqrt 3 := by
    rw [←Real.sqrt_sq (norm_nonneg (ringComplex lambda)),
      ringComplex_norm_sq_eq_absNorm_span,absNorm_span_lambda]
    norm_num
  rw [map_mul,map_pow,norm_mul,norm_pow,norm_ringComplex_unit,one_mul,hl,
    Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma ramified_radial_decay (u : Oˣ) (m : ℕ) :
    ‖ringComplex ((u:O)*lambda^m)‖^(1/3:ℝ)/‖ringComplex ((u:O)*lambda^m)‖=
      1/(3:ℝ)^((m:ℝ)/3) := by
  rw [ramified_unit_norm,←Real.rpow_mul (by norm_num),
    ←Real.rpow_sub (by norm_num)]
  conv_rhs => rw [one_div,←Real.rpow_neg (by norm_num)]
  congr 1
  ring

def completedCuspArrayIndex (u : Oˣ) (m : ℕ) (I J : Ideal O) : O :=
  ((u:O)*lambda^m)*primaryIdealGenerator I*(primaryIdealGenerator J)^3

def completedCuspArrayEligible (I J : Ideal O) : Prop :=
  Squarefree I ∧ primaryIdealGenerator I≠0 ∧ primaryIdealGenerator J≠0

/-- A positive cusp constant independent of the ramified and ideal indices. -/
def completedCuspArrayConstant (s : FixedCuspSector) : ℝ :=
  1+‖-2*Real.pi*Complex.I*thetaFrequencyScale‖/
    (sourceCuspScale (fixedCuspIndex s))^2*sourceCuspCoefficientBaseBound (fixedCuspIndex s)

lemma completedCuspArrayConstant_pos (s : FixedCuspSector) :
    0<completedCuspArrayConstant s := by
  have h := sourceCuspCoefficientBaseBound_nonneg (fixedCuspIndex s)
  unfold completedCuspArrayConstant
  positivity

def completedCuspArrayWeight (m : ℕ) (I J : Ideal O) : ℝ :=
  (3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)

lemma completedCuspArrayWeight_pos (m : ℕ) (I J : Ideal O)
    (hI : primaryIdealGenerator I≠0) (hJ : primaryIdealGenerator J≠0) :
    0<completedCuspArrayWeight m I J := by
  have hi : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      primaryIdealGenerator_ne_zero_ideal I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      primaryIdealGenerator_ne_zero_ideal J hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  unfold completedCuspArrayWeight
  positivity

lemma completedCuspArray_bound (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (m : ℕ) (I J : Ideal O)
    (h : completedCuspArrayEligible I J) :
    ‖fixedCuspPeriodicArray N c s b (completedCuspArrayIndex u m I J)‖≤
      completedCuspArrayConstant s/completedCuspArrayWeight m I J := by
  let q : ThetaFullIndex := (u,m,(⟨I,h.1,h.2.1⟩,⟨J,h.2.2⟩))
  have he := fixedCuspPeriodicArray_full_bound N c s b q
  change ‖fixedCuspPeriodicArray N c s b (completedCuspArrayIndex u m I J)‖≤
    (‖-2*Real.pi*Complex.I*thetaFrequencyScale‖/
      (sourceCuspScale (fixedCuspIndex s))^2*sourceCuspCoefficientBaseBound (fixedCuspIndex s))*
      (‖ringComplex ((u:O)*lambda^m)‖^(1/3:ℝ)/‖ringComplex ((u:O)*lambda^m)‖)/
      (‖ringComplex (primaryIdealGenerator I)‖*‖ringComplex (primaryIdealGenerator J)‖^2) at he
  rw [ramified_radial_decay,primaryIdealGenerator_norm I h.2.1,
    primaryIdealGenerator_norm J h.2.2,Real.sq_sqrt (Nat.cast_nonneg _)] at he
  apply he.trans
  rw [show (‖-2*Real.pi*Complex.I*thetaFrequencyScale‖/
      (sourceCuspScale (fixedCuspIndex s))^2*sourceCuspCoefficientBaseBound (fixedCuspIndex s))*
      (1/(3:ℝ)^((m:ℝ)/3))/(Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))=
      (completedCuspArrayConstant s-1)/completedCuspArrayWeight m I J by
    unfold completedCuspArrayConstant completedCuspArrayWeight
    ring]
  exact div_le_div_of_nonneg_right (by linarith)
    (completedCuspArrayWeight_pos m I J h.2.1 h.2.2).le

/-- The actual periodic cusp array, normalized to absolute value at most one. -/
def completedCuspArray (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (m : ℕ) (I J : Ideal O) : ℂ :=
  if completedCuspArrayEligible I J then
    fixedCuspPeriodicArray N c s b (completedCuspArrayIndex u m I J)*
      (completedCuspArrayWeight m I J:ℂ)/(completedCuspArrayConstant s:ℂ)
  else 0

lemma completedCuspArray_norm (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (m : ℕ) (I J : Ideal O) :
    ‖completedCuspArray N c s b u m I J‖≤1 := by
  by_cases h : completedCuspArrayEligible I J
  · have hw := completedCuspArrayWeight_pos m I J h.2.1 h.2.2
    have hc := completedCuspArrayConstant_pos s
    rw [completedCuspArray,if_pos h,norm_div,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg hw.le,Complex.norm_real,Real.norm_of_nonneg hc.le]
    apply (div_le_one hc).mpr
    exact (le_div_iff₀ hw).mp (completedCuspArray_bound N c s b u m I J h)
  · simp only [completedCuspArray,if_neg h,norm_zero,zero_le_one]

lemma completedCuspArray_reconstruct (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (m : ℕ) (I J : Ideal O)
    (h : completedCuspArrayEligible I J) :
    fixedCuspPeriodicArray N c s b (completedCuspArrayIndex u m I J)=
      (completedCuspArrayConstant s:ℂ)*completedCuspArray N c s b u m I J/
        (completedCuspArrayWeight m I J:ℂ) := by
  have hw : (completedCuspArrayWeight m I J:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (completedCuspArrayWeight_pos m I J h.2.1 h.2.2).ne'
  have hc : (completedCuspArrayConstant s:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (completedCuspArrayConstant_pos s).ne'
  rw [completedCuspArray,if_pos h]
  field_simp

end CompletedGauss

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
