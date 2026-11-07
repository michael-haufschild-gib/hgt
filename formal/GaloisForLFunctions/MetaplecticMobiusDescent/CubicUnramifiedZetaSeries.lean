/-
Unramified ideal series adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicPrimaryIdealGenerators

/-!
# Unramified ideal zeta and totient series

The primary generator embeds unramified ideals injectively in the planar
Eisenstein lattice, giving absolute convergence for `Re s > 1`.
Ideal Möbius inversion gives the reciprocal series and nonvanishing.
The totient convolution then gives `Σ φ(I)N(I)^(-s)=Z(s-1)/Z(s)`
for `Re s > 2`, with the ramified ideal excluded throughout.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

def unramifiedNormWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := if primaryIdealGenerator I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)
  map_zero' := by simp
  map_one' := by
    rw [primaryIdealGenerator_one,if_neg one_ne_zero,map_one,Nat.cast_one,Complex.one_cpow]
  map_mul' I J := by
    by_cases hI : primaryIdealGenerator I=0
    · simp [primaryIdealGenerator_mul,hI]
    by_cases hJ : primaryIdealGenerator J=0
    · simp [primaryIdealGenerator_mul,hJ]
    simp only [primaryIdealGenerator_mul,mul_eq_zero,hI,hJ,false_or,ite_false,map_mul,Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

lemma unramifiedNormWeight_of_good (s : ℂ) (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    unramifiedNormWeight s I=(Ideal.absNorm I:ℂ)^(-s) := if_neg hI

lemma unramifiedNormWeight_of_bad (s : ℂ) (I : Ideal O) (hI : primaryIdealGenerator I=0) :
    unramifiedNormWeight s I=0 := if_pos hI

lemma primaryIdealGenerator_injective_good :
    Function.Injective (fun I : GoodIdeal => primaryIdealGenerator I.1) := by
  intro I J h
  dsimp only at h
  apply Subtype.ext
  rw [← (primaryIdealGenerator_spec I.1 I.2).1,← (primaryIdealGenerator_spec J.1 J.2).1,h]

lemma norm_unramifiedNormWeight (s : ℂ) (I : GoodIdeal) :
    ‖unramifiedNormWeight s I.1‖=‖ringComplex (primaryIdealGenerator I.1)‖^(-2*s.re) := by
  rw [unramifiedNormWeight_of_good s I.1 I.2]
  have hnorm : ‖ringComplex (primaryIdealGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [ringComplex_norm_sq_eq_absNorm_span,(primaryIdealGenerator_spec I.1 I.2).1]
  have hn : 0<‖ringComplex (primaryIdealGenerator I.1)‖ :=
    norm_pos_iff.mpr (ringComplex_ne_zero I.2)
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖ringComplex (primaryIdealGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
  rw [← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖unramifiedNormWeight s I‖) := by
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective
    primaryIdealGenerator_injective_good
  have hsub : Summable (fun I : GoodIdeal => ‖unramifiedNormWeight s I.1‖) := by
    simpa only [Function.comp_def, norm_unramifiedNormWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | primaryIdealGenerator I ≠ 0})
    (f := fun I => ‖unramifiedNormWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : primaryIdealGenerator I=0
  · simp [Set.indicator,hI,unramifiedNormWeight_of_bad s I hI]
  · simp [Set.indicator,hI]

lemma norm_ideal_moebius_le_one (I : Ideal O) : ‖(moebius I:ℂ)‖≤1 := by
  by_cases hI : Squarefree I
  · simp [hI.moebius_eq]
  · simp [moebius_of_not_squarefree hI]

lemma moebius_unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖(moebius I:ℂ)*unramifiedNormWeight s I‖) := by
  apply (unramifiedNormWeight_summable_norm s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one I)

def unramifiedIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O, unramifiedNormWeight s I

def unramifiedMobiusSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I:ℂ)*unramifiedNormWeight s I


theorem unramifiedMobiusSeries_mul_zeta (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s*unramifiedIdealZeta s=1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs).mul_norm
    (unramifiedNormWeight_summable_norm s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=if B=1 then 1 else 0 := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,zero_ne_one,ite_false]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ))*unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B; simp only [map_one,mul_one]
          · simp only [zero_mul]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p,F p)=1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O,
        ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs)
        (unramifiedNormWeight_summable_norm s hs)
    _ = ∑' p,F p := by
      apply tsum_congr
      intro p
      simp only [F,map_mul]
      ring
    _ = 1 := hFone

theorem unramifiedIdealZeta_ne_zero (s : ℂ) (hs : 1<s.re) : unramifiedIdealZeta s ≠ 0 := by
  intro hz
  have h := unramifiedMobiusSeries_mul_zeta s hs
  rw [hz,mul_zero] at h
  exact zero_ne_one h

theorem unramifiedMobiusSeries_eq_inv (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s=(unramifiedIdealZeta s)⁻¹ := by
  have h := unramifiedMobiusSeries_mul_zeta s hs
  calc
    _ = (unramifiedMobiusSeries s*unramifiedIdealZeta s)*(unramifiedIdealZeta s)⁻¹ := by
      field_simp [unramifiedIdealZeta_ne_zero s hs]
    _ = _ := by rw [h,one_mul]

lemma unramifiedNormWeight_shift (s : ℂ) (I : Ideal O) :
    unramifiedNormWeight (s-1) I=(Ideal.absNorm I:ℂ)*unramifiedNormWeight s I := by
  by_cases hg : primaryIdealGenerator I=0
  · rw [unramifiedNormWeight_of_bad _ I hg,unramifiedNormWeight_of_bad _ I hg,mul_zero]
  · rw [unramifiedNormWeight_of_good _ I hg,unramifiedNormWeight_of_good _ I hg]
    have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal I hg))
    rw [show -(s-1)=(1:ℂ)+(-s) by ring,Complex.cpow_add _ _ hn,Complex.cpow_one]

lemma mulFiber_totient_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))=(idealTotient B:ℂ) := by
  let e := mulFiberDivisorEquiv B hB
  have hp (p : MulFiber B) :
      (moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ)=
        (Ideal.absNorm B:ℂ)*((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := by
    have hI : p.1.1 ≠ 0 := by
      intro hz
      have hh := p.2
      rw [hz,zero_mul] at hh
      exact hB hh.symm
    have hn : (Ideal.absNorm p.1.1:ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have heq : (Ideal.absNorm B:ℂ)=(Ideal.absNorm p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ) := by
      calc
        _ = (Ideal.absNorm (p.1.1*p.1.2):ℂ) := congrArg (fun I => (Ideal.absNorm I:ℂ)) p.2.symm
        _ = _ := by rw [map_mul,Nat.cast_mul]
    rw [heq]
    field_simp
  calc
    _ = ∑' p : MulFiber B,(Ideal.absNorm B:ℂ)*
        ((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := tsum_congr hp
    _ = (Ideal.absNorm B:ℂ)*
        ∑' D : {D : Ideal O // D ∈ idealDivisors B},
          ((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)) := by
      rw [← tsum_mul_left]
      exact e.tsum_eq (fun D => (Ideal.absNorm B:ℂ)*((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)))
    _ = (Ideal.absNorm B:ℂ)*
        ∑ D ∈ idealDivisors B,((moebius D:ℂ)/(Ideal.absNorm D:ℂ)) := by
      rw [tsum_fintype]
      apply congrArg (fun z : ℂ => (Ideal.absNorm B:ℂ)*z)
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (moebius D:ℂ)/(Ideal.absNorm D:ℂ))).symm
    _ = _ := (idealTotient_moebius B hB).symm

def unramifiedTotientSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O,(idealTotient I:ℂ)*unramifiedNormWeight s I

theorem unramifiedTotientSeries_product (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedMobiusSeries s*unramifiedIdealZeta (s-1) := by
  have hs1 : 1<s.re := by linarith
  have hs2 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*(Ideal.absNorm p.2:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs1).mul_norm
    (unramifiedNormWeight_summable_norm (s-1) hs2)
  have heq (p : Ideal O × Ideal O) :
      ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight (s-1) p.2=F p := by
    simp only [F,unramifiedNormWeight_shift,map_mul]
    ring
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=
      (idealTotient B:ℂ)*unramifiedNormWeight s B := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,map_zero,mul_zero]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))*
            unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by rw [mulFiber_totient_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = ∑' p,F p := hsum.tsum_eq
    _ = _ := by
      rw [unramifiedMobiusSeries,unramifiedIdealZeta,
        tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs1)
          (unramifiedNormWeight_summable_norm (s-1) hs2)]
      exact tsum_congr (fun p => (heq p).symm)

theorem unramifiedTotientSeries_quotient (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedIdealZeta (s-1)/unramifiedIdealZeta s := by
  rw [unramifiedTotientSeries_product s hs,unramifiedMobiusSeries_eq_inv s (by linarith),div_eq_mul_inv]
  ring

lemma idealTotient_le_absNorm (I : Ideal O) (hI : I ≠ 0) :
    idealTotient I ≤ Ideal.absNorm I := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  change Nat.card (O ⧸ I)ˣ ≤ Nat.card (O ⧸ I)
  exact Nat.card_le_card_of_injective (Units.val : (O ⧸ I)ˣ → O ⧸ I) Units.val_injective

theorem unramifiedTotientSeries_summable_norm (s : ℂ) (hs : 2<s.re) :
    Summable (fun I : Ideal O => ‖(idealTotient I:ℂ)*unramifiedNormWeight s I‖) := by
  have hs1 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  apply (unramifiedNormWeight_summable_norm (s-1) hs1).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  by_cases hI : I=0
  · subst I; simp only [map_zero,mul_zero,norm_zero,le_refl]
  · rw [norm_mul,Complex.norm_natCast,unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (idealTotient_le_absNorm I hI)) (norm_nonneg _)


#print axioms unramifiedIdealZeta_ne_zero
#print axioms unramifiedTotientSeries_quotient
#print axioms unramifiedTotientSeries_summable_norm
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
