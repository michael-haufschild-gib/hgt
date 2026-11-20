import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedCrossingsBetweenTwoWalls
import GaloisForLFunctions.RHTower.MobiusMertensMeanSquareExponentLaw
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# The fixed and crossing interval Gram of a Möbius matching

The reading at an integer cut is a sum of signed interval indicators.
Its complete second moment is their Gram form: each pair is charged the
number of cuts in its overlap. Adding a terminal interval for each fixed
vertex gives the Mertens mean square for every admissible matching. The
growth exponent of this signed pair sum therefore reads the zero abscissa.
-/

namespace GaloisForLFunctions.RestrictedFactorizationCalculus
open Finset Filter _root_.RHTower ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching
noncomputable section
open scoped Classical ArithmeticFunction.Moebius

/-- The sum of interval charges visible at x. -/
def cutReading (S : Finset ℕ) (u : ℕ → ℕ) (c : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ S, if n≤x ∧ x<u n then c n else 0

/-- Number of shared cuts at most X. Empty or reversed intervals cost zero. -/
def sharedCuts (X m n a b : ℕ) := min (X+1) (min a b) - max m n

/-- Products of two different readings retain each signed pair of charges
with its exact overlap, including nested intervals and tied endpoints. -/
theorem mixed_cut_gram (S T : Finset ℕ) (u v : ℕ → ℕ) (c d : ℕ → ℝ) (X : ℕ) :
    ∑ x ∈ range (X+1), cutReading S u c x * cutReading T v d x =
      ∑ m ∈ S, ∑ n ∈ T, c m*d n*sharedCuts X m n (u m) (v n) := by
  let term (m n x : ℕ) := if (m≤x ∧ x<u m) ∧ (n≤x ∧ x<v n) then c m*d n else 0
  have hx (x : ℕ) : cutReading S u c x * cutReading T v d x =
      ∑ m ∈ S, ∑ n ∈ T, term m n x := by
    rw [cutReading,cutReading,sum_mul]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    by_cases hm : m≤x ∧ x<u m <;> by_cases hn : n≤x ∧ x<v n <;> simp [term,hm,hn]
  rw [sum_congr rfl (fun x _ => hx x),sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  have support : (range (X+1)).filter (fun x => (m≤x ∧ x<u m) ∧ (n≤x ∧ x<v n)) =
      Ico (max m n) (min (X+1) (min (u m) (v n))) := by
    ext x
    simp only [mem_filter,mem_range,mem_Ico,max_le_iff,lt_min_iff]
    tauto
  simp only [term,←sum_filter,support,sum_const,Nat.card_Ico,nsmul_eq_mul,sharedCuts]
  ring

private theorem crossing_eq_cut (F : ℕ → ℕ) {Y X : ℕ} (hYX : Y≤X) :
    crossingSignedPrefix F Y = cutReading (Icc 1 X) F (fun n => (μ n:ℝ)) Y := by
  have hs : Icc 1 Y ⊆ Icc 1 X := fun n hn => mem_Icc.mpr
    ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hYX⟩
  rw [cutReading,← sum_subset hs (fun n hn hout => by
    have hh : ¬n≤Y := fun h => hout (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,h⟩)
    simp [hh]),crossingSignedPrefix,sum_filter]
  exact sum_congr rfl fun n hn => by simp only [(mem_Icc.mp hn).2,true_and]

/-- The two crossing prefixes can come from unrelated matchings or from
arbitrary endpoint maps. Every pair retains its signed overlap length. -/
theorem signed_crossing_mixed_overlap (F G : ℕ → ℕ) (X : ℕ) :
    ∑ x ∈ range (X+1), crossingSignedPrefix F x*crossingSignedPrefix G x =
      ∑ m ∈ Icc 1 X, ∑ n ∈ Icc 1 X, (μ m:ℝ)*(μ n:ℝ)*sharedCuts X m n (F m) (G n) := by
  rw [← mixed_cut_gram]
  refine sum_congr rfl fun x hx => ?_
  have hle : x≤X := by have := mem_range.mp hx; omega
  rw [crossing_eq_cut F hle,crossing_eq_cut G hle]

/-- Fixed squarefree vertices remain visible to the last cut. A moving
lower endpoint disappears as soon as its matched upper endpoint is reached. -/
def matchingIntervalEnd (F : ℕ → ℕ) (X n : ℕ) :=
  if Squarefree n ∧ F n=n then X+1 else F n

/-- The signed matching Gram, formed from pairs of integer intervals. -/
def matchingOverlap (F : ℕ → ℕ) (X : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 X, ∑ n ∈ Icc 1 X, (μ m:ℝ)*(μ n:ℝ)*
    sharedCuts X m n (matchingIntervalEnd F X m) (matchingIntervalEnd F X n)

private theorem charge_eq_cut (F : ℕ → ℕ) {Y X : ℕ} (hYX : Y≤X) :
    cutReading (Icc 1 X) (matchingIntervalEnd F X) (fun n => (μ n:ℝ)) Y =
      fixedSignedPrefix F Y + crossingSignedPrefix F Y := by
  have hs : Icc 1 Y ⊆ Icc 1 X := fun n hn => mem_Icc.mpr
    ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hYX⟩
  rw [cutReading,← sum_subset hs (fun n hn h => by
    have hny : ¬n≤Y := fun hh => h (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,hh⟩)
    simp [hny])]
  simp only [fixedSignedPrefix,squarefreeOf,crossingSignedPrefix,sum_filter,← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hny := (mem_Icc.mp hn).2
  have hy : Y<X+1 := by omega
  by_cases he : F n=n
  · by_cases hs : Squarefree n <;> simp [matchingIntervalEnd,hs,he,hny,hy,hny.not_gt]
  · by_cases hs : Squarefree n <;> simp [matchingIntervalEnd,hs,he,hny]

/-- Equality of overlap energies for every admissible involution. The
off-diagonal pairs keep the Möbius signs of both lower endpoints. -/
theorem matchingOverlap_eq_mertens (F : ℕ → ℕ) (hF : ∀ n : ℕ, Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) (X : ℕ) :
    matchingOverlap F X = ∑ x ∈ range (X+1), shiftedMertensReal x^2 := by
  rw [matchingOverlap,← mixed_cut_gram]
  refine sum_congr rfl fun x hx => ?_
  have hle : x≤X := by have := mem_range.mp hx; omega
  rw [charge_eq_cut F hle,fixed_add_crossing F hF,← sq]
  congr 1
  rw [shiftedMertensReal_eq]
  simp [coprimeMoebiusSum,coprimeMoebiusIndicator]

/-- The power exponent of the signed overlap table determines the same
zero-free half-plane for every admissible matching. -/
theorem matchingOverlap_exponent (F : ℕ → ℕ) (hF : ∀ n : ℕ, Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) {c : ℝ} (hc : 1≤c)
    (hne : c≠2*zetaZeroAbscissa+1) :
    (∃ C : ℝ, ∀ X : ℕ, matchingOverlap F X ≤ C*((X:ℝ)+1)^c) ↔ 2*zetaZeroAbscissa+1<c := by
  simp_rw [matchingOverlap_eq_mertens F hF]
  exact exists_sum_sq_shiftedMertens_le_rpow_iff hc hne

/-- All overlap exponents above 2σ+1 are available precisely when the
zero abscissa is at most σ. This form includes the boundary. -/
theorem matchingOverlap_halfplane (F : ℕ → ℕ) (hF : ∀ n : ℕ, Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) {σ : ℝ} (hσ : 1/2≤σ) :
    (∀ c>2*σ+1, ∃ C : ℝ, ∀ X : ℕ, matchingOverlap F X≤C*((X:ℝ)+1)^c) ↔
      zetaZeroAbscissa≤σ := by
  constructor
  · intro h
    by_contra! hθ
    let c := σ+zetaZeroAbscissa+1
    have hc : 2*σ+1<c := by dsimp [c]; linarith only [hθ]
    have hc' : c < 2*zetaZeroAbscissa+1 := by dsimp [c]; linarith only [hθ]
    have hg := (matchingOverlap_exponent F hF (by linarith only [hc,hσ]) hc'.ne).mp (h c hc)
    exact hg.not_gt hc'
  · intro h c hc
    have hc' : 2*zetaZeroAbscissa+1<c := by linarith only [h,hc]
    exact (matchingOverlap_exponent F hF (by linarith only [hc,hσ]) hc'.ne').mpr hc'

/-- At every prescribed relative displacement there exists one short
matching whose unpaid vertices have that upper density and whose signed
interval overlaps give an exact RH criterion. -/
theorem sparse_matching_overlap_iff_rh {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℕ → ℕ, (∀ n : ℕ, Squarefree n → F (F n)=n ∧
        (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n|≤ε*n) ∧
      (∀ᶠ X : ℕ in Filter.atTop, ((prefixUnpaid F X).card:ℝ)≤ε*X) ∧
      ((∀ c : ℝ, c>2 → ∃ C : ℝ, ∀ X : ℕ, matchingOverlap F X≤C*((X:ℝ)+1)^c) ↔ RiemannHypothesis) := by
  obtain ⟨F,hF,_,hd,_⟩ := one_sparse_fixed_set_detects_every_mertens_power hε
  refine ⟨F,hF,hd,?_⟩
  have hb := matchingOverlap_halfplane F (fun n hn => ⟨(hF n hn).1,(hF n hn).2.1⟩)
    (σ:=1/2) le_rfl
  rw [show (2:ℝ)*(1/2)+1=2 by norm_num] at hb
  exact hb.trans ⟨fun h => zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mp
    (le_antisymm h half_le_zetaZeroAbscissa),fun h =>
      (zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr h).le⟩


end
end GaloisForLFunctions.RestrictedFactorizationCalculus
