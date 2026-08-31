import GaloisForLFunctions.HTGeometry.RegularElementDepthDrop
import GaloisForLFunctions.HTGeometry.LinearNonzerodivisor
import GaloisForLFunctions.HTGeometry.ReesDepth
import GaloisForLFunctions.HTGeometry.QuotientRegularSequence

/-!
# A regular sequence can be taken linear

Over an infinite field every step of a regular sequence inside the irrelevant ideal can be replaced
by a linear form:

```text
map_smul_top                  the image of I • ⊤ under a quotient map is I • ⊤
smul_top_lt_top_quotSMul      properness survives quotienting by an element of the ideal
linearForm_mem_irrelevantIdeal
exists_linear_isRegular       ** a regular sequence of length n gives a linear one of length n **
```

The induction is the expected one, and both of its inputs are now available: a linear nonzerodivisor
exists because the associated primes miss the degree-one part
(`exists_linearForm_isSMulRegular`), and quotienting by it drops the depth by exactly one
(`subsingleton_ext_quotSMul`), so Rees converts back and forth at each step.  The properness side
condition is the graded Nakayama argument: if the irrelevant ideal were everything on the quotient
it would be everything upstairs, since the element quotiented by already lies in it.

Linearity is what a degeneration argument needs: linear forms are homogeneous for the standard
grading, so quotienting by them keeps the flat family graded with finitely generated pieces over the
base line.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory MvPolynomial
open scoped Pointwise

universe u

theorem map_smul_top {R : Type u} [CommRing R] {I : Ideal R} {M : ModuleCat.{u} R} {u : R} :
    Submodule.map (Submodule.mkQ (u • (⊤ : Submodule R M))) (I • (⊤ : Submodule R M))
      = I • (⊤ : Submodule R (M ⧸ (u • (⊤ : Submodule R M)))) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap, Submodule.mkQ_apply]
    rw [show Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) (r • m)
      = r • Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) m from rfl]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [Submodule.smul_le]
    intro r hr z _
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (u • (⊤ : Submodule R M)) z
    refine ⟨r • x, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]

theorem smul_top_le_of_mem {R : Type u} [CommRing R] {I : Ideal R} {M : ModuleCat.{u} R} {u : R}
    (hu : u ∈ I) : u • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
  intro z hz
  rw [Submodule.mem_smul_pointwise_iff_exists] at hz
  obtain ⟨m, -, hm⟩ := hz
  rw [← hm]
  exact Submodule.smul_mem_smul hu Submodule.mem_top

/-- **Properness survives quotienting by an element of the ideal.** -/
theorem smul_top_lt_top_quotSMul {R : Type u} [CommRing R] {I : Ideal R} {M : ModuleCat.{u} R}
    {u : R} (hu : u ∈ I) (h : I • (⊤ : Submodule R M) < ⊤) :
    I • (⊤ : Submodule R (ModuleCat.of R (M ⧸ (u • (⊤ : Submodule R M))))) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro htop
  refine absurd (le_antisymm le_top ?_) (ne_of_lt h)
  intro x _
  have hx : Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) x
      ∈ Submodule.map (Submodule.mkQ (u • (⊤ : Submodule R M))) (I • (⊤ : Submodule R M)) := by
    rw [map_smul_top,
      show I • (⊤ : Submodule R (M ⧸ (u • (⊤ : Submodule R M)))) = ⊤ from htop]
    trivial
  obtain ⟨y, hy, hxy⟩ := hx
  have hdiff : x - y ∈ u • (⊤ : Submodule R M) := by
    have hz : Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) (x - y) = 0 := by
      rw [Submodule.Quotient.mk_sub,
        show Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) y
          = Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) x from hxy, sub_self]
    rwa [Submodule.Quotient.mk_eq_zero] at hz
  have hrw : x = y + (x - y) := by abel
  rw [hrw]
  exact Submodule.add_mem _ hy (smul_top_le_of_mem hu hdiff)

variable {N : ℕ} {K : Type u} [Field K]

theorem linearForm_mem_irrelevantIdeal (c : Fin N → K) :
    linearForm c ∈ irrelevantIdeal K (Fin N) := by
  rw [linearForm]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **A regular sequence can be taken linear.**  Over an infinite field, each step of the sequence
can be replaced by a linear form: one exists because the associated primes miss the degree-one part,
and quotienting by it drops the depth by exactly one. -/
theorem exists_linear_isRegular [Infinite K] :
    ∀ (n : ℕ) (M : ModuleCat.{u} (MvPolynomial (Fin N) K)),
      Module.Finite (MvPolynomial (Fin N) K) M →
      irrelevantIdeal K (Fin N) • (⊤ : Submodule (MvPolynomial (Fin N) K) M) < ⊤ →
      (∃ rs : List (MvPolynomial (Fin N) K), rs.length = n ∧
        (∀ r ∈ rs, r ∈ irrelevantIdeal K (Fin N)) ∧ RingTheory.Sequence.IsRegular M rs) →
      ∃ cs : List (Fin N → K), cs.length = n ∧
        RingTheory.Sequence.IsRegular M (cs.map linearForm) := by
  intro n
  induction n with
  | zero =>
    intro M hfin hlt _
    refine ⟨[], rfl, ⟨⟨fun i hi => absurd hi (by simp)⟩, ?_⟩⟩
    intro htop
    rw [List.map_nil,
      show (Ideal.ofList ([] : List (MvPolynomial (Fin N) K))) = ⊥ by simp [Ideal.ofList],
      Submodule.bot_smul] at htop
    exact absurd (le_antisymm le_top (htop.le.trans bot_le)) (ne_of_lt hlt)
  | succ n ih =>
    intro M hfin hlt hseq
    haveI := hfin
    -- the first entry gives an element of the irrelevant ideal that is regular
    obtain ⟨rs, hlen, hmem, hreg⟩ := hseq
    have hpos : 0 < rs.length := by omega
    have hr0mem : rs[0] ∈ irrelevantIdeal K (Fin N) := hmem _ (List.getElem_mem hpos)
    have hr0reg : IsSMulRegular M rs[0] := by
      have h0 := hreg.regular_mod_prev 0 hpos
      rw [show (rs.take 0) = [] from rfl,
        show (Ideal.ofList ([] : List (MvPolynomial (Fin N) K))) = ⊥ by simp [Ideal.ofList],
        Submodule.bot_smul] at h0
      exact (isSMulRegular_congr (Submodule.quotEquivOfEqBot ⊥ rfl) rs[0]).mp h0
    obtain ⟨c, hc⟩ := exists_linearForm_isSMulRegular (M := (M : Type u)) hr0mem hr0reg
    -- pass to the quotient
    have hltq := smul_top_lt_top_quotSMul (I := irrelevantIdeal K (Fin N)) (M := M)
      (u := linearForm c) (linearForm_mem_irrelevantIdeal c) hlt
    have hextM := ext_subsingleton_of_isRegular (irrelevantIdeal K (Fin N)) (n + 1) M hlt
      ⟨rs, hlen, hmem, hreg⟩
    have hextQ := subsingleton_ext_quotSMul (X := ModuleCat.of (MvPolynomial (Fin N) K)
        (Shrink.{u} (MvPolynomial (Fin N) K ⧸ irrelevantIdeal K (Fin N)))) hc hextM
    haveI : Module.Finite (MvPolynomial (Fin N) K)
        (ModuleCat.of (MvPolynomial (Fin N) K)
          ((M : Type u) ⧸ (linearForm c • (⊤ : Submodule (MvPolynomial (Fin N) K) M)))) :=
      Module.Finite.quotient _ _
    obtain ⟨ss, hslen, hsmem, hsreg⟩ := exists_isRegular_of_ext (irrelevantIdeal K (Fin N)) n
      (ModuleCat.of (MvPolynomial (Fin N) K)
        ((M : Type u) ⧸ (linearForm c • (⊤ : Submodule (MvPolynomial (Fin N) K) M))))
      hltq hextQ
    obtain ⟨cs, hcslen, hcsreg⟩ := ih _ inferInstance hltq ⟨ss, hslen, hsmem, hsreg⟩
    refine ⟨c :: cs, by simp [hcslen], ?_⟩
    rw [List.map_cons, RingTheory.Sequence.isRegular_cons_iff]
    exact ⟨hc, hcsreg⟩

end GaloisForLFunctions.HTGeometry
