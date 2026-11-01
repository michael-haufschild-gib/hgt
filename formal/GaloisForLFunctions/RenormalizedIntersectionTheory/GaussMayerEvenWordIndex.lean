import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveWordCoding

/-! The actual reversed Gauss digit convention gives an exact bijection
between nonempty even source words and nonempty words of digit pairs. -/

open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCoding MayerGaussCoding MayerWords
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEvenWordIndex

theorem ofFn_asWord (ds : List ℕ) : List.ofFn (asWord ds) = ds := by
  induction ds with
  | nil => simp only [asWord,List.ofFn_zero]
  | cons d ds ih =>
    simp only [asWord,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,ih]

theorem pairedDigits_injective : Function.Injective pairedDigits := by
  intro ps qs he
  apply pairedRunWord_injective
  apply matrixWord_injective
  have h := congrArg (fun ds : List ℕ => wordMatrix ds.length (asWord ds)) he
  simpa only [pairedDigits_matrix] using h

private theorem ofFn_cast {m n : ℕ} (h : m = n) (a : Word m) :
    List.ofFn (h ▸ a) = List.ofFn a := by
  subst n
  rfl

theorem evenWordPairs_injective (k : ℕ) : Function.Injective (evenWordPairs k) := by
  intro a b he
  apply List.ofFn_inj.mp
  rw [← evenWordPairs_digits,← evenWordPairs_digits,he]

theorem evenWordPairs_surjective (k : ℕ) (ps : List (ℕ × ℕ)) (hps : ps.length = k) :
    ∃ a : Word (2*k), evenWordPairs k a = ps := by
  have hl : (pairedDigits ps).length = 2*k := by rw [pairedDigits_length,hps]
  let a : Word (2*k) := hl ▸ asWord (pairedDigits ps)
  refine ⟨a,pairedDigits_injective ?_⟩
  rw [evenWordPairs_digits]
  exact (ofFn_cast hl _).trans (ofFn_asWord _)

/-- All nonempty even words of the actual source, indexed by half-length minus one. -/
abbrev EvenWord := Σ n : ℕ, Word (2*n+2)

def toPairs (a : EvenWord) : List (ℕ × ℕ) := evenWordPairs (a.1+1) a.2

theorem toPairs_length (a : EvenWord) : (toPairs a).length = a.1+1 :=
  evenWordPairs_length _ _

theorem toPairs_ne_nil (a : EvenWord) : toPairs a ≠ [] := by
  intro he
  have h := congrArg List.length he
  rw [toPairs_length,List.length_nil] at h
  omega

theorem toPairs_injective : Function.Injective toPairs := by
  rintro ⟨n,a⟩ ⟨m,b⟩ he
  have hlen := congrArg List.length he
  rw [toPairs_length,toPairs_length] at hlen
  have hnm : n = m := by simpa only [Nat.add_right_cancel_iff] using hlen
  subst m
  have hab : a = b := evenWordPairs_injective (n+1) he
  subst b
  rfl

theorem toPairs_surjective (ps : List (ℕ × ℕ)) (hps : ps ≠ []) :
    ∃ a : EvenWord, toPairs a = ps := by
  have hl : ps.length-1+1 = ps.length := Nat.sub_add_cancel (List.length_pos_iff.mpr hps)
  obtain ⟨a,ha⟩ := evenWordPairs_surjective (ps.length-1+1) ps hl.symm
  exact ⟨⟨ps.length-1,a⟩,ha⟩

/-- Exact source-to-pair reindexing, retaining every Gauss digit. -/
def evenWordPairEquiv : EvenWord ≃ {ps : List (ℕ × ℕ) // ps ≠ []} :=
  Equiv.ofBijective (fun a => ⟨toPairs a,toPairs_ne_nil a⟩) ⟨
    fun _ _ h => toPairs_injective (congrArg Subtype.val h),
    fun ps => by
      obtain ⟨a,ha⟩ := toPairs_surjective ps.val ps.property
      exact ⟨a,Subtype.ext ha⟩⟩

#print axioms pairedDigits_injective
#print axioms toPairs_length
#print axioms evenWordPairEquiv
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEvenWordIndex
