import GaloisForLFunctions.HTGeometry.BorelWeil.CechSupport

/-!
# Čech vanishing for monomial cochains, with support control

A cochain of the Čech complex of a cover by `|T|` opens, whose values are finitely supported
functions on a set `A` of basis vectors (Laurent monomials), each basis vector `a` being regular
exactly on the charts containing a prescribed set `supp a`, splits in every degree `p ≥ 0` as soon
as no basis vector that occurs has `supp a = T`: for each occurring `a` the cone operator of an index
outside `supp a` contracts the `a`-component.  This is `cech_vanishing_of_supp_ne_univ` with two
refinements needed for the Čech computation of `𝒪(-e)` on projective space:

* the degree may be `0` (the augmented complex, whose degree `-1` term is the global sections);
* the primitive only involves basis vectors that occur in the cocycle, so any further condition on
  the occurring basis vectors (total degree, nonnegativity of the fibre exponents) is inherited.
-/

namespace HTGeometry

open GaloisForLFunctions.HTGeometry.BorelWeil Finset

variable {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T]
variable {A : Type*} [DecidableEq A] {k : Type*} [CommRing k]

/-- The Čech differential on finitely supported values. -/
noncomputable def monoCechD (ω : Finset T → (A →₀ k)) : Finset T → (A →₀ k) :=
  fun I => ∑ u ∈ I, (cechSign I u : k) • ω (I.erase u)

omit [Fintype T] [DecidableEq A] in
theorem monoCechD_apply (ω : Finset T → (A →₀ k)) (I : Finset T) (a : A) :
    (monoCechD ω I) a = cechD (fun J => (ω J) a) I := by
  rw [monoCechD, Finsupp.finsetSum_apply, cechD]
  exact Finset.sum_congr rfl fun u _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-- **Čech vanishing away from the full support, in every degree, with support control.** -/
theorem monoCech_vanishing [Nonempty T] {supp : A → Finset T} {p : ℕ}
    {ω : Finset T → (A →₀ k)} (hcard : ∀ I : Finset T, I.card ≠ p + 1 → ω I = 0)
    (hchart : ∀ (I : Finset T) (a : A), a ∈ (ω I).support → supp a ⊆ I)
    (hδ : monoCechD ω = 0)
    (hne : ∀ (I : Finset T) (a : A), a ∈ (ω I).support → supp a ≠ Finset.univ) :
    ∃ η : Finset T → (A →₀ k),
      (∀ I : Finset T, I.card ≠ p → η I = 0) ∧
      (∀ (I : Finset T) (a : A), a ∈ (η I).support → supp a ⊆ I) ∧
      (∀ (I : Finset T) (a : A), a ∈ (η I).support → ∃ J : Finset T, a ∈ (ω J).support) ∧
      monoCechD η = ω := by
  classical
  have hlocal : ∀ a : A, cechD (fun J => (ω J) a) = 0 := by
    intro a
    funext I
    rw [← monoCechD_apply ω I a, hδ]
    simp
  have hchoice : ∀ a : A, ∃ u : T, ((∃ I : Finset T, a ∈ (ω I).support) → u ∉ supp a) := by
    intro a
    by_cases hex : ∃ I : Finset T, a ∈ (ω I).support
    · obtain ⟨I, hI⟩ := hex
      have hproper : supp a ≠ Finset.univ := hne I a hI
      obtain ⟨u, hu⟩ : ∃ u, u ∉ supp a := by
        by_contra hcon
        push Not at hcon
        exact hproper (Finset.eq_univ_iff_forall.mpr hcon)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨Classical.arbitrary T, fun h => absurd h hex⟩
  choose u₀ hu₀ using hchoice
  set S : Finset A := Finset.univ.biUnion (fun J : Finset T => (ω J).support) with hS
  have hmemS : ∀ (I : Finset T) (a : A),
      (cechH (u₀ a) (fun J => (ω J) a)) I ≠ 0 → a ∈ S := by
    intro I a ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have hne0 : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at ha
        exact ha rfl
      exact Finset.mem_biUnion.mpr ⟨insert (u₀ a) I, Finset.mem_univ _,
        Finsupp.mem_support_iff.mpr hne0⟩
  refine ⟨fun I => Finsupp.onFinset S (fun a => (cechH (u₀ a) (fun J => (ω J) a)) I)
    (fun a ha => hmemS I a ha), ?_, ?_, ?_, ?_⟩
  · intro I hI
    ext a
    simp only [Finsupp.onFinset_apply, Finsupp.coe_zero, Pi.zero_apply]
    rw [cechH]
    by_cases h : u₀ a ∈ I
    · rw [if_pos h]
    · rw [if_neg h]
      have hcard' : (insert (u₀ a) I).card ≠ p + 1 := by
        rw [Finset.card_insert_of_notMem h]
        omega
      rw [hcard _ hcard']
      simp
  · intro I a ha
    rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
    rw [cechH] at ha
    by_cases h : u₀ a ∈ I
    · rw [if_pos h] at ha; exact absurd rfl ha
    · rw [if_neg h] at ha
      have hne0 : (ω (insert (u₀ a) I)) a ≠ 0 := by
        intro hz; rw [hz, mul_zero] at ha; exact ha rfl
      have hsub := hchart _ a (Finsupp.mem_support_iff.mpr hne0)
      have hnot : u₀ a ∉ supp a := hu₀ a ⟨insert (u₀ a) I, Finsupp.mem_support_iff.mpr hne0⟩
      intro j hj
      rcases Finset.mem_insert.mp (hsub hj) with rfl | hji
      · exact absurd hj hnot
      · exact hji
  · intro I a ha
    rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply] at ha
    have := hmemS I a ha
    obtain ⟨J, -, hJ⟩ := Finset.mem_biUnion.mp this
    exact ⟨J, hJ⟩
  · funext I
    ext a
    rw [monoCechD_apply]
    have hfun : (fun J => (Finsupp.onFinset S
        (fun b => (cechH (u₀ b) (fun K => (ω K) b)) J) (fun b hb => hmemS J b hb)) a)
        = cechH (u₀ a) (fun K => (ω K) a) := by
      funext J
      rw [Finsupp.onFinset_apply]
    rw [hfun]
    have hid := cechD_cechH_add (u₀ a) (fun K => (ω K) a) I
    rw [hlocal a] at hid
    simpa using hid

end HTGeometry
