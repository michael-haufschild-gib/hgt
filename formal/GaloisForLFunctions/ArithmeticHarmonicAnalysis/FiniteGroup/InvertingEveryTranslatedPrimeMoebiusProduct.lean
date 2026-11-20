import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.FullPrimeFrequencySupportOfTheMoebiusAmbiguity
import Mathlib.Analysis.Fourier.ZMod

/-!
# Recovering a cyclic signal from translated Möbius products

At each prime period at least five, any lag supplies a convolution
kernel with no nonzero-frequency zeros. Prescribing the total signal
mass restores the possible missing constant mode. The range and the
inverse are explicit, including the compatibility of the measured mean.
-/
noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {p : ℕ} [Fact p.Prime]
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
local notation "A" => cyclicAmbiguityAmplitude (cyclicMoebiusProfile p)

/-- Convolution with the two Möbius values separated by b; t is the
translate of the readout. -/
def translatedMoebiusReading (b : ZMod p) (g : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  ∑ x, (cyclicMoebiusProfile p (x+b)*conj (cyclicMoebiusProfile p x))*g (t-x)

private theorem spectrum_of_translates (b a : ZMod p) (g : ZMod p → ℂ) :
    ZMod.dft (translatedMoebiusReading b g) a=A a b*ZMod.dft g a := by
  let r := fun x : ZMod p => cyclicMoebiusProfile p (x+b)*conj (cyclicMoebiusProfile p x)
  change (∑ t,χ (-(t*a))*(∑ x,r x*g (t-x))) =
    (∑ x,r x*χ (-(a*x)))*(∑ y,χ (-(y*a))*g y)
  calc _ = ∑ x,∑ t,χ (-(t*a))*(r x*g (t-x)) := by
         simp_rw [mul_sum]; rw [sum_comm]
       _ = ∑ x,(r x*χ (-(a*x)))*(∑ y,χ (-(y*a))*g y) := by
         refine sum_congr rfl fun x _ => ?_
         have he := Fintype.sum_equiv (Equiv.addRight x)
           (fun y : ZMod p => χ (-((y+x)*a))*(r x*g (y+x-x)))
           (fun t : ZMod p => χ (-(t*a))*(r x*g (t-x))) (fun _ => rfl)
         rw [←he,mul_sum]
         refine sum_congr rfl fun y _ => ?_
         rw [add_sub_cancel_right,show -((y+x)*a)= -(a*x)+ -(y*a) by ring,AddChar.map_add_eq_mul]
         ring
       _ = _ := (sum_mul ..).symm

private theorem nonzero_mode {a : ZMod p} (hp : 5 ≤ p) (ha : a ≠ 0) (b : ZMod p) : A a b≠0 := by
  intro hz
  have hw := every_nonzero_prime_moebius_frequency ha hp b
  simp only [cyclicAmbiguityWeight,hz,norm_zero,zero_pow (by norm_num : 2≠0),lt_self_iff_false] at hw

/-- Inverting the occupied Fourier modes and prescribing the constant
mode produces the unique signal with the given sum and readouts. -/
def decodeMoebiusTranslates (b : ZMod p) (s : ℂ) (y : ZMod p → ℂ) : ZMod p → ℂ :=
  ZMod.dft.symm (fun a => if a=0 then s else ZMod.dft y a/A a b)

theorem decode_moebius_translates_exactly (b : ZMod p) (hp : 5 ≤ p) (g : ZMod p → ℂ) :
    decodeMoebiusTranslates b (∑ x,g x) (translatedMoebiusReading b g)=g := by
  apply ZMod.dft.injective
  rw [decodeMoebiusTranslates,LinearEquiv.apply_symm_apply]
  funext a
  by_cases ha : a=0
  · subst a; simp [ZMod.dft_apply_zero]
  · rw [if_neg ha,spectrum_of_translates,mul_div_cancel_left₀ _ (nonzero_mode hp ha b)]

/-- Exact range: the sum of the measured translates is the prescribed
signal sum times the ordinary Möbius autocorrelation at this lag. -/
theorem unique_signal_from_moebius_translates_iff (b : ZMod p) (hp : 5 ≤ p) (s : ℂ) (y : ZMod p → ℂ) :
    (∃! g : ZMod p → ℂ, (∑ x,g x)=s ∧ translatedMoebiusReading b g=y) ↔
      (∑ t,y t)=A 0 b*s := by
  constructor
  · rintro ⟨g,⟨hs,rfl⟩,_⟩
    simpa only [ZMod.dft_apply_zero,hs] using spectrum_of_translates b 0 g
  · intro hmean
    let g := decodeMoebiusTranslates b s y
    have hg (a : ZMod p) : ZMod.dft g a=if a=0 then s else ZMod.dft y a/A a b :=
      congrFun (ZMod.dft.apply_symm_apply _) a
    have hsum : ∑ x,g x=s := by simpa [ZMod.dft_apply_zero] using hg 0
    have he : translatedMoebiusReading b g=y := by
      apply ZMod.dft.injective
      funext a
      rw [spectrum_of_translates,hg]
      by_cases ha : a=0
      · subst a; simpa [ZMod.dft_apply_zero] using hmean.symm
      · rw [if_neg ha,←mul_div_assoc,mul_div_cancel_left₀ _ (nonzero_mode hp ha b)]
    refine ⟨g,⟨hsum,he⟩,?_⟩
    rintro g' ⟨hs',he'⟩
    have h := decode_moebius_translates_exactly b hp g'
    rw [hs',he'] at h
    exact h.symm

/-- With the signal sum known, any one translate can be erased. For
any two prescribed erasures there are distinct signals of sum zero
whose readings agree everywhere else. -/
theorem moebius_translates_identify_iff_one_erasure (b : ZMod p) (hp : 5 ≤ p)
    (S : Set (ZMod p)) :
    (∀ g h : ZMod p → ℂ, (∑ x, g x) = ∑ x, h x →
      Set.EqOn (translatedMoebiusReading b g) (translatedMoebiusReading b h) S → g = h) ↔
      Sᶜ.Subsingleton := by
  classical
  constructor
  · intro identify u hu v hv
    by_contra huv
    let y (t : ZMod p) : ℂ := (if t = u then 1 else 0) - (if t = v then 1 else 0)
    have hy : ∑ t, y t = 0 := by simp [y, sum_sub_distrib]
    obtain ⟨g,⟨hg,hr⟩,_⟩ :=
      (unique_signal_from_moebius_translates_iff b hp 0 y).mpr (by simpa only [mul_zero] using hy)
    have he : g = 0 := by
      apply identify
      · simpa only [Pi.zero_apply,sum_const_zero] using hg
      · intro t ht
        have htu : t ≠ u := fun e => hu (e ▸ ht)
        have htv : t ≠ v := fun e => hv (e ▸ ht)
        rw [hr]
        simp [y,htu,htv,translatedMoebiusReading]
    have h := congrFun hr u
    simp [he,translatedMoebiusReading,y,huv] at h
  · intro erased g h hs hagree
    have hmass (f : ZMod p → ℂ) :
        (∑ t,translatedMoebiusReading b f t) = A 0 b * ∑ x,f x := by
      simpa only [ZMod.dft_apply_zero] using spectrum_of_translates b 0 f
    have hzero : ∑ t,(translatedMoebiusReading b g t-translatedMoebiusReading b h t) = 0 := by
      rw [sum_sub_distrib,hmass,hmass,hs,sub_self]
    have hr : translatedMoebiusReading b g = translatedMoebiusReading b h := by
      funext a
      by_cases ha : a ∈ S
      · exact hagree ha
      · apply sub_eq_zero.mp
        have hoff (t : ZMod p) (_ : t ∈ univ) (hne : t ≠ a) :
            translatedMoebiusReading b g t - translatedMoebiusReading b h t = 0 := by
          apply sub_eq_zero.mpr
          apply hagree
          by_contra ht
          exact hne (erased ht ha)
        rwa [sum_eq_single_of_mem a (mem_univ a) hoff] at hzero
    calc g = decodeMoebiusTranslates b (∑ x,g x) (translatedMoebiusReading b g) :=
           (decode_moebius_translates_exactly b hp g).symm
         _ = h := by rw [hs,hr,decode_moebius_translates_exactly b hp]

#print axioms decode_moebius_translates_exactly
#print axioms unique_signal_from_moebius_translates_iff
#print axioms moebius_translates_identify_iff_one_erasure
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
