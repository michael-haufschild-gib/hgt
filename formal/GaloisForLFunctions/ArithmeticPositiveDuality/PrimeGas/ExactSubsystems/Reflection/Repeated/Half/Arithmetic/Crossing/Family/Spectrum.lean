import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Zeros.Bound

/-! # Exceptional probe ratios of an arbitrary finite energy spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family

open Finset Set
open _root_.HTGeometry (finiteGibbsPartition)

variable {I J : Type*} [Fintype I] [Fintype J]

def agrees (E : I → ℝ) (t : ℝ) : Prop :=
  finiteGibbsPartition t (centered E) = finiteGibbsPartition (-t) (centered E)

theorem reflection_agrees {E : I → ℝ} (h : Reflects E) (t : ℝ) : agrees E t := by
  have pair := (pairs_iff_matches _ _).mp ((reflects_iff_centered_pair E).mp h)
  unfold agrees
  rw [partition_negative]
  simpa only [zero_sub] using partition_congr pair t

theorem agrees_odd (E : I → ℝ) (t : ℝ) : agrees E t ↔ oddTrace (centered E) t = 0 := by
  rw [oddTrace_eq,sub_eq_zero]
  exact eq_comm

theorem agrees_abs (E : I → ℝ) (t : ℝ) : agrees E |t| ↔ agrees E t := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    simp only [agrees,neg_neg]
    exact eq_comm

/-- Intrinsic reflection is invisible at every temperature. A false positive is a
positive temperature that passes the comparison on an asymmetric spectrum. -/
def blind (E : I → ℝ) := {t : ℝ | 0 < t ∧ agrees E t ∧ ¬Reflects E}

theorem finite_blind (E : I → ℝ) : (blind E).Finite := by
  by_cases symm : Reflects E
  · have empty : blind E = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun _ h => h.2.2 symm
    rw [empty]; exact Set.finite_empty
  · obtain ⟨u,hu⟩ : ∃ u : ℝ, oddTrace (centered E) u ≠ 0 := by
      by_contra! all
      exact symm ((centered_heat_iff_reflects E).mp fun j _ _ => (agrees_odd E j).mpr (all j))
    by_contra infinite
    obtain ⟨Z,inc,size⟩ := Set.Infinite.exists_subset_card_eq infinite (Fintype.card I)
    have bound := Zeros.size_bound (sum_centered E) hu Z
      (fun t ht => ⟨(inc ht).1,(agrees_odd E t).mp (inc ht).2.1⟩)
    omega

def ratios (E : I → ℝ) : Set ℝ :=
  (fun p : ℝ × ℝ => p.1/p.2) '' (blind E ×ˢ blind E)

theorem finite_ratios (E : I → ℝ) : (ratios E).Finite :=
  ((finite_blind E).prod (finite_blind E)).image _

/-- The same-spectrum quotient classifies all positive probe ratios, including
spectra with repeated levels and spectra that reflect intrinsically. -/
theorem pair_iff (E : I → ℝ) {r : ℝ} (hr : 0 < r) :
    (∀ d : ℝ, (agrees E d ∧ agrees E (r*d) ↔ d=0 ∨ Reflects E)) ↔ r ∉ ratios E := by
  constructor
  · rintro all ⟨⟨x,y⟩,⟨hx,hy⟩,eq⟩
    have scale : r*y=x := ((div_eq_iff hy.1.ne').mp eq).symm
    exact ((all y).mp ⟨hy.2.1,by rw [scale]; exact hx.2.1⟩).elim hy.1.ne' hy.2.2
  · intro good d
    constructor
    · rintro ⟨first,second⟩
      by_contra! h
      have pos := abs_pos.mpr h.1
      have atSecond : agrees E (r*|d|) := by
        simpa only [abs_mul,abs_of_pos hr] using (agrees_abs E (r*d)).mpr second
      exact good ⟨(r*|d|,|d|),⟨⟨mul_pos hr pos,atSecond,h.2⟩,⟨pos,(agrees_abs E d).mpr first,h.2⟩⟩,
        mul_div_cancel_right₀ r pos.ne'⟩
    · rintro (rfl | reflecting)
      · simp only [agrees,mul_zero,neg_zero,and_self]
      · exact ⟨reflection_agrees reflecting _,reflection_agrees reflecting _⟩

theorem agrees_congr {E : I → ℝ} {F : J → ℝ} (h : Matches E F) (t : ℝ) :
    agrees E t ↔ agrees F t := by
  simp only [agrees,partition_congr (Observation.centered_matches h)]

omit [Fintype I] [Fintype J] in
theorem reflects_congr {E : I → ℝ} {F : J → ℝ} (h : Matches E F) :
    Reflects E ↔ Reflects F := exists_congr fun d => Mixed.pairs_congr h d

#print axioms finite_blind
#print axioms pair_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family
