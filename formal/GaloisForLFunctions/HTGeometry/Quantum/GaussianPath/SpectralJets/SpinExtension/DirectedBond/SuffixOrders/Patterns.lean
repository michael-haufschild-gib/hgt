import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ProductRank

/-! # The complete family of directed suffix words -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Stop the suffix, or record the terminal multiplicity and continue one
site to the left. -/
def Pattern : ℕ→Type
  | 0 => Unit
  | n+1 => Option (Bool × Pattern n)

instance patternFintype : (n : ℕ) → Fintype (Pattern n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := patternFintype n; inferInstanceAs (Fintype (Option (Bool × Pattern n)))

def patternWord : (n : ℕ) → Pattern n → List (Fin n)
  | 0,_ => []
  | _+1,none => []
  | n+1,some (j,p) => letters j (patternWord n p)

theorem option_pattern_card (n : ℕ) : Fintype.card (Option (Pattern n))=2^(n+1) := by
  induction n with
  | zero => change Fintype.card (Option Unit)=2^1; simp
  | succ n ih =>
    rw [Fintype.card_option] at ih
    change Fintype.card (Option (Option (Bool × Pattern n)))=2^((n+1)+1)
    rw [Fintype.card_option,Fintype.card_option,Fintype.card_prod,Fintype.card_bool,pow_succ _ (n+1),←ih]
    omega

private theorem Suffix.encode {n : ℕ} {w : List (Fin n)} (h : Suffix n w) :
    ∃ p : Pattern n, patternWord n p=w := by
  induction h with
  | empty n =>
    cases n with
    | zero => exact ⟨(),rfl⟩
    | succ n => exact ⟨none,rfl⟩
  | append j _ ih =>
    obtain ⟨p,rfl⟩ := ih
    exact ⟨some (j,p),rfl⟩

/-- Every combinatorially allowed suffix occurs exactly once among the
nonconstant rows of any nonsingular directed minor. -/
theorem enumerate_minor {n : ℕ} {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (hcard : Fintype.card I=2^(n+1)) (j : Bool) (k : I) (w : I→List (Fin (n+1)))
    (hw : ∀ i, ∃ u, Suffix n u ∧ w i=letters j u)
    (read : List (Fin (n+1))→I→R)
    (hd : (of fun i l => if i=k then 1 else read (w i) l).det≠0) :
    ∃ e : I≃Option (Pattern n), e k=none ∧
      ∀ i p, e i=some p → w i=letters j (patternWord n p) := by
  classical
  have hc (i) : ∃ p : Pattern n, w i=letters j (patternWord n p) := by
    obtain ⟨u,hu,hi⟩ := hw i
    obtain ⟨p,hp⟩ := hu.encode
    exact ⟨p,hp.symm ▸ hi⟩
  choose code hcode using hc
  let e (i : I) : Option (Pattern n) := if i=k then none else some (code i)
  have hin : Function.Injective e := by
    intro i l hil
    by_contra hne
    apply hd (Matrix.det_zero_of_row_eq hne (funext fun a => ?_))
    by_cases hi : i=k <;> by_cases hl : l=k
    · exact (hne (hi.trans hl.symm)).elim
    · simp [e,hi,hl] at hil
    · simp [e,hi,hl] at hil
    · have h := Option.some.inj (show some (code i)=some (code l) by simpa only [e,if_neg hi,if_neg hl] using hil)
      simp only [of_apply,if_neg hi,if_neg hl,hcode i,hcode l,h]
  let E := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr
    ⟨hin,hcard.trans (option_pattern_card n).symm⟩)
  refine ⟨E,by change e k=none; simp [e],?_⟩
  intro i p hp
  change e i=some p at hp
  by_cases hi : i=k
  · simp [e,hi] at hp
  · rw [e,if_neg hi] at hp
    exact (Option.some.inj hp) ▸ hcode i

#print axioms enumerate_minor
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
