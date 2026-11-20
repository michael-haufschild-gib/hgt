import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.TheSquarefreePairsInEveryCyclicMoebiusFrequencyRow
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PeakReadingsIdentifyTheAnnihilatorOfTheAmbiguitySupport
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Full nonzero frequency support at prime periods

At a prime period, a nontrivial Fourier coefficient of an integer
profile vanishes exactly when the entire profile is constant. Every
translated Möbius product at period at least five contains a nonzero
entry, by squarefree overlap, and a zero entry, supplied by 4.
Consequently every nonzero frequency is occupied at every lag.
-/
noncomputable section
open Finset Complex ArithmeticFunction
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {p : ℕ} [Fact p.Prime]
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod p) ℂ)

private def primeIndices : ZMod p ≃ Fin p where
  toFun x := ⟨x.val,ZMod.val_lt x⟩
  invFun i := (i.val:ZMod p)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)

/-- Cyclotomic rigidity of each nonzero Fourier mode, for arbitrary
integer data on the prime cycle. -/
theorem integer_prime_fourier_zero_iff_constant (f : ZMod p → ℤ) {a : ZMod p} (ha : a ≠ 0) :
    (∑ x,(f x:ℂ)*χ (-(a*x)))=0 ↔ ∀ x y,f x=f y := by
  have hp : p.Prime := Fact.out
  let ζ := χ (-a)
  have hpow (j : ℕ) : ζ^j=χ (-(a*(j:ZMod p))) := by
    rw [show ζ^j=χ (j • (-a)) from (AddChar.map_nsmul_eq_pow χ j (-a)).symm,nsmul_eq_mul]
    congr 1; ring
  have hroot : IsPrimitiveRoot ζ p := by
    apply isPrimitiveRoot_of_mem_nthRootsFinset hp
    · apply (Polynomial.mem_nthRootsFinset hp.pos (1:ℂ)).mpr
      simp only [hpow,ZMod.natCast_self,mul_zero,neg_zero,AddChar.map_zero_eq_one]
    · intro he
      have hz : χ (-a)=χ 0 := by simpa only [AddChar.map_zero_eq_one] using he
      exact ha (neg_eq_zero.mp (ZMod.injective_stdAddChar hz))
  let e := primeIndices (p:=p)
  let g := fun i : Fin p => f (i.val:ZMod p)
  have hs : (∑ x,(f x:ℂ)*χ (-(a*x)))=∑ i : Fin p,(g i:ℂ)*ζ^i.val := by
    refine Fintype.sum_equiv e _ _ fun x => ?_
    change (f x:ℂ)*χ (-(a*x))=(f (x.val:ZMod p):ℂ)*ζ^x.val
    rw [hpow,ZMod.natCast_zmod_val]
  rw [hs,IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hroot g]
  constructor
  · intro h x y
    have he := h (e x) (e y)
    change f (x.val:ZMod p)=f (y.val:ZMod p) at he
    simpa only [ZMod.natCast_zmod_val] using he
  · exact fun h i j => h _ _

/-- The complete nonzero frequency axis occurs in every Möbius
ambiguity row over a prime field of at least five elements. -/
theorem every_nonzero_prime_moebius_frequency {a : ZMod p} (ha : a ≠ 0)
    (hp : 5 ≤ p) (b : ZMod p) :
    0 < cyclicAmbiguityWeight (cyclicMoebiusProfile p) a b := by
  let f := fun x : ZMod p => (moebius ((x+b).val+1):ℤ)*moebius (x.val+1)
  have hA : cyclicAmbiguityAmplitude (cyclicMoebiusProfile p) a b =
      ∑ x,(f x:ℂ)*χ (-(a*x)) := by
    unfold cyclicAmbiguityAmplitude
    refine sum_congr rfl fun x _ => ?_
    simp only [cyclicMoebiusProfile,f,Int.cast_mul,map_intCast]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  rw [hA]
  intro hz
  have hconst := (integer_prime_fourier_zero_iff_constant f ha).mp hz
  have hprime : 0 < (p:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos := (div_pos hprime (by norm_num : (0:ℝ)<36)).trans_le (squarefree_cyclic_overlap_lower p b)
  have hne : 0 < (squarefreeCyclicPairs p b).card := Nat.cast_pos.mp hpos
  obtain ⟨x,hx⟩ := card_pos.mp hne
  obtain ⟨hs,hs'⟩ := (mem_filter.mp hx).2
  have hfx : f x ≠ 0 := mul_ne_zero (moebius_ne_zero_iff_squarefree.mpr hs')
    (moebius_ne_zero_iff_squarefree.mpr hs)
  let z : ZMod p := ((3:ℕ):ZMod p)
  have hval : z.val+1=4 := by rw [show z.val=3 from ZMod.val_natCast_of_lt (by omega : 3<p)]
  have hm4 : (moebius 4 : ℤ)=0 := moebius_eq_zero_of_not_squarefree (by
    intro h
    exact (Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two) (by norm_num))
  apply hfx
  rw [hconst x z]
  simp only [f,hval,hm4,mul_zero]

/-- The only remaining zeros of the full two-dimensional diagram are
the ordinary integer autocorrelation zeros at frequency zero. -/
theorem prime_moebius_ambiguity_zero_iff (hp : 5 ≤ p) (a b : ZMod p) :
    cyclicAmbiguityWeight (cyclicMoebiusProfile p) a b=0 ↔
      a=0 ∧ (∑ x : ZMod p,(moebius ((x+b).val+1):ℤ)*moebius (x.val+1))=0 := by
  by_cases ha : a=0
  · subst a
    have he : cyclicAmbiguityAmplitude (cyclicMoebiusProfile p) 0 b =
        (((∑ x : ZMod p,(moebius ((x+b).val+1):ℤ)*moebius (x.val+1)):ℤ):ℂ) := by
      simp only [cyclicAmbiguityAmplitude,cyclicMoebiusProfile,zero_mul,neg_zero,
        AddChar.map_zero_eq_one,mul_one,map_intCast,Int.cast_sum,Int.cast_mul]
    simp only [cyclicAmbiguityWeight,he,sq_eq_zero_iff,norm_eq_zero,Int.cast_eq_zero,
      true_and]
  · simp only [ha,false_and,iff_false]
    exact (every_nonzero_prime_moebius_frequency ha hp b).ne'

/-- Every nonzero displacement strictly lowers the peak. Orthogonality
to the two occupied sites (1,0) and (1,1) forces both coordinates to vanish. -/
theorem unique_prime_moebius_ambiguity_peak (hp : 5 ≤ p) (x : ZMod p × ZMod p) :
    cyclicAmbiguityWeight (cyclicMoebiusProfile p) x.1 x.2 =
      cyclicAmbiguityWeight (cyclicMoebiusProfile p) 0 0 ↔ x=0 := by
  constructor
  · intro he
    have h := (ambiguity_peak_iff_annihilator (cyclicMoebiusProfile p) x).mp he
    have hm (b : ZMod p) : ((1,b): ZMod p × ZMod p) ∈ ambiguitySupport (cyclicMoebiusProfile p) :=
      mem_filter.mpr ⟨mem_univ _,every_nonzero_prime_moebius_frequency one_ne_zero hp b⟩
    have hz : x.2=0 := by simpa only [symplecticIndex,mul_zero,mul_one,zero_sub,neg_eq_zero] using h (1,0) (hm 0)
    have hx : x.1=0 := by simpa only [symplecticIndex,mul_one,hz,sub_zero] using h (1,1) (hm 1)
    exact Prod.ext hx hz
  · rintro rfl; rfl

#print axioms integer_prime_fourier_zero_iff_constant
#print axioms every_nonzero_prime_moebius_frequency
#print axioms prime_moebius_ambiguity_zero_iff
#print axioms unique_prime_moebius_ambiguity_peak
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
