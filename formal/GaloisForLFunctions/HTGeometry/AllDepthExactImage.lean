import GaloisForLFunctions.HTGeometry.AllDepthRealization

/-!
# The exact image of the pair-face signature

Every compatible family of finite class divisors is the pair-face signature of a member of the
all-depth mixed-constraint class.

* `finite_line_support_of_divFiniteClasses`, `mixedConstGermSet_of_erase`;
* **`exists_class_member_with_prescribed_pairSig`**.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A divisor with finitely many classes meets every free transverse line finitely. -/
theorem finite_line_support_of_divFiniteClasses {H : AddSubgroup ℂ} {D : ℂ → ℂ}
    (hfin : DivFiniteClasses H D) {t : ℂ} (ht : ∀ n : ℤ, (n : ℂ) * t ∈ H → n = 0) (p : ℂ) :
    (Function.support fun n : ℤ => D (p + (n : ℂ) * t)).Finite := by
  classical
  obtain ⟨S, hS⟩ := hfin
  have hsub : (Function.support fun n : ℤ => D (p + (n : ℂ) * t))
      ⊆ ⋃ q ∈ (S : Set ℂ), {n : ℤ | p + (n : ℂ) * t - q ∈ H} := by
    intro n hn
    obtain ⟨q, hq, hmem⟩ := hS _ hn
    exact Set.mem_biUnion (by exact_mod_cast hq) hmem
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun q _ => ?_) hsub
  refine Set.Subsingleton.finite ?_
  intro n₁ h₁ n₂ h₂
  have hm₁ : p + (n₁ : ℂ) * t - q ∈ H := h₁
  have hm₂ : p + (n₂ : ℂ) * t - q ∈ H := h₂
  have hrel : ((n₁ - n₂ : ℤ) : ℂ) * t ∈ H := by
    have hdiff := sub_mem hm₁ hm₂
    have harg : p + (n₁ : ℂ) * t - q - (p + (n₂ : ℂ) * t - q) = ((n₁ - n₂ : ℤ) : ℂ) * t := by
      push_cast
      ring
    rwa [harg] at hdiff
  have := ht _ hrel
  omega

/-- **A member of the class of a smaller direction set lies in the class of the larger one, with
constant zero.** -/
theorem mixedConstGermSet_of_erase (τ : ι → ℂ) (s : Finset ι) {k : ι} (hk : k ∈ s)
    {c₀ : ℂ} {f : ℂ → ℂ} (h : MixedConstGermSet τ (s \ {k}) f c₀) :
    MixedConstGermSet τ s f 0 := by
  classical
  have hkunion : ({k} : Finset ι) ∪ (s \ ({k} : Finset ι)) = s := by
    ext m
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (rfl | hm)
      · exact hk
      · exact hm.1
    · intro hm
      by_cases hmk : m = k
      · exact Or.inl hmk
      · exact Or.inr ⟨hm, hmk⟩
  have hkdisj : Disjoint ({k} : Finset ι) (s \ ({k} : Finset ι)) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    exact (Finset.mem_sdiff.mp hm').2 hm
  intro z
  have hcube : HTGeometry.diffCube τ s f
      = HTGeometry.shiftDiffFun (τ k) (HTGeometry.diffCube τ (s \ {k}) f) := by
    have h1 := HTGeometry.diffCube_union τ hkdisj f
    rw [hkunion, HTGeometry.diffCube_singleton] at h1
    exact h1
  rw [hcube]
  have hpull := (tendsto_nhdsNE_add_const z (τ k)).eventually (h (z + τ k))
  filter_upwards [hpull, h z] with wv h1 h2
  show HTGeometry.diffCube τ (s \ {k}) f (wv + τ k) - HTGeometry.diffCube τ (s \ {k}) f wv = 0
  rw [h1, h2, sub_self]

/-! ## The realization -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Every compatible family of finite class divisors is a pair-face signature.** -/
theorem exists_class_member_with_prescribed_pairSig
    (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im) (hQ : PeriodsIntegrallyIndependent τ) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → 2 ≤ n →
      ∀ D : ι → ι → ℤ → ℂ → ℂ,
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 →
          DivInvariant (tripticPeriodGroup (τ j) (τ i)) (D i j ℓ)) →
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 →
          DivFiniteClasses (tripticPeriodGroup (τ j) (τ i)) (D i j ℓ)) →
        (∃ N : ℕ, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p, D i j ℓ p = 0) →
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → D i j ℓ = D j i ℓ) →
        (∀ i ∈ s, ∀ j ∈ s, ∀ l ∈ s, i ≠ j → i ≠ l → j ≠ l → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
          (∑ᶠ n : ℤ, D i j ℓ (p + (n : ℂ) * τ l))
            = ∑ᶠ n : ℤ, D i l ℓ (p + (n : ℂ) * τ j)) →
        ∃ (f : ℂ → ℂ) (Cst : ℂ),
          MeromorphicOn f (Set.univ : Set ℂ) ∧ PeriodicOneGerm f ∧
          MixedConstGermSet τ s f Cst ∧
          ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → ∀ p,
            pairSig τ s f i j ℓ p = D i j ℓ p := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hcard hn D hinv hfin htopex hsymm htriple
  obtain ⟨N, htop⟩ := htopex
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · -- depth two
    obtain ⟨i₀, j₀, hij₀, hs⟩ := Finset.card_eq_two.mp (by omega : s.card = 2)
    subst hs
    have hi₀ : i₀ ∈ ({i₀, j₀} : Finset ι) := Finset.mem_insert_self i₀ {j₀}
    have hj₀ : j₀ ∈ ({i₀, j₀} : Finset ι) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self j₀)
    have hwit : ∀ g : ℂ → ℂ, pairFaceWitnessFun τ ({i₀, j₀} : Finset ι) i₀ j₀ g = g := by
      intro g
      rw [pairFaceWitnessFun, Finset.sdiff_self]
      funext z
      simp [HTGeometry.diffCube]
    obtain ⟨Y, C, hYmero, hYper, hYmixed, hYsig⟩ :=
      exists_depthTwo_member_with_prescribed_divisor (hτ j₀) (hτ i₀)
        (indepPeriods_of_periodsIntegrallyIndependent τ hQ hij₀) (D i₀ j₀) N
        (fun ℓ hℓ => hinv i₀ hi₀ j₀ hj₀ hij₀ ℓ hℓ)
        (fun ℓ hℓ => hfin i₀ hi₀ j₀ hj₀ hij₀ ℓ hℓ)
        (fun ℓ hℓ p => htop i₀ hi₀ j₀ hj₀ hij₀ ℓ hℓ p)
    have hYmixedSet : MixedConstGermSet τ ({i₀, j₀} : Finset ι) Y C :=
      (mixedConstGermSet_pair_iff hij₀).mpr hYmixed
    refine ⟨Y, C, hYmero, hYper, hYmixedSet, ?_⟩
    intro i hi j hj hij ℓ hℓ p
    have hmain : pairSig τ ({i₀, j₀} : Finset ι) Y i₀ j₀ ℓ p = D i₀ j₀ ℓ p := by
      rw [pairSig, hwit]
      exact hYsig ℓ hℓ p
    have hpairs : (i = i₀ ∧ j = j₀) ∨ (i = j₀ ∧ j = i₀) := by
      have hi' : i = i₀ ∨ i = j₀ := by simpa using hi
      have hj' : j = i₀ ∨ j = j₀ := by simpa using hj
      rcases hi' with rfl | rfl
      · rcases hj' with rfl | rfl
        · exact absurd rfl hij
        · exact Or.inl ⟨rfl, rfl⟩
      · rcases hj' with rfl | rfl
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd rfl hij
    rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hmain
    · rw [h1, h2, pairSig_symm τ hτ hQ _ (Ne.symm hij₀) hj₀ hi₀ hYmero hYper hYmixedSet hℓ p,
        hmain, hsymm i₀ hi₀ j₀ hj₀ hij₀ ℓ hℓ]
  · -- depth at least three
    obtain ⟨k, hk⟩ : ∃ k, k ∈ s := Finset.card_pos.mp (by omega)
    have hcard' : (s \ ({k} : Finset ι)).card = n - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hk, hcard]
    obtain ⟨a, ha'⟩ : ∃ a, a ∈ s \ ({k} : Finset ι) := Finset.card_pos.mp (by omega)
    have hak : a ≠ k := by simpa using (Finset.mem_sdiff.mp ha').2
    have hmemS : ∀ i ∈ s \ ({k} : Finset ι), i ∈ s := fun i hi => (Finset.mem_sdiff.mp hi).1
    have hneK : ∀ i ∈ s \ ({k} : Finset ι), i ≠ k := fun i hi => by
      simpa using (Finset.mem_sdiff.mp hi).2
    -- realize the components through `k`
    obtain ⟨F₀, Cst₀, hF₀mero, hF₀per, hF₀mixed, hF₀sig⟩ :=
      exists_bottom_realizer τ hτ hQ s hk hak (fun i => D i k) N
        (fun i hi ℓ hℓ => hinv i (hmemS i hi) k hk (hneK i hi) ℓ hℓ)
        (fun i hi ℓ hℓ => hfin i (hmemS i hi) k hk (hneK i hi) ℓ hℓ)
        (fun i hi ℓ hℓ p => htop i (hmemS i hi) k hk (hneK i hi) ℓ hℓ p)
        (by
          intro i hi j hj ℓ hℓ p
          by_cases hij : i = j
          · rw [hij]
          · have h1 := htriple i (hmemS i hi) k hk j (hmemS j hj) (hneK i hi) hij
              (fun hcon => (hneK j hj) hcon.symm) ℓ hℓ p
            have h2 := htriple j (hmemS j hj) k hk i (hmemS i hi) (hneK j hj) (Ne.symm hij)
              (fun hcon => (hneK i hi) hcon.symm) ℓ hℓ p
            rw [h1, h2, hsymm j (hmemS j hj) i (hmemS i hi) (Ne.symm hij) ℓ hℓ])
    -- the residual error on the pairs below `k`
    set E : ι → ι → ℤ → ℂ → ℂ :=
      fun i j ℓ p => D i j ℓ p - pairSig τ s F₀ i j ℓ p with hE
    have hEinv : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → DivInvariant (tripticPeriodGroup (τ j) (τ i)) (E i j ℓ) :=
      fun i hi j hj hij ℓ hℓ =>
        DivInvariant.sub (hinv i (hmemS i hi) j (hmemS j hj) hij ℓ hℓ)
          (divInvariant_pairSig τ s hij (hmemS i hi) (hmemS j hj) hF₀mero hF₀per hF₀mixed hℓ)
    have hEfin : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → DivFiniteClasses (tripticPeriodGroup (τ j) (τ i)) (E i j ℓ) :=
      fun i hi j hj hij ℓ hℓ =>
        DivFiniteClasses.sub (hfin i (hmemS i hi) j (hmemS j hj) hij ℓ hℓ)
          (divFiniteClasses_pairSig τ s hij (hmemS i hi) (hmemS j hj) hF₀mero hF₀per hF₀mixed
            (hτ j) hℓ)
    have hkfree : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ nn : ℤ, nn • (-τ k) ∈ tripticPeriodGroup (τ j) (τ i) → nn = 0 := by
      intro i hi j hj hij nn hmem
      have hneg : (-nn) = 0 := by
        refine tripticPeriodGroup_free τ hQ (hneK i hi) (hneK j hj) (-nn) ?_
        have harg : (-nn) • τ k = nn • (-τ k) := by
          rw [neg_zsmul, smul_neg]
        rw [harg]
        exact hmem
      omega
    -- the error has vanishing pushforward along `τ k`
    have hEpush : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ, (∑ᶠ nn : ℤ, E i j ℓ (p + (nn : ℂ) * τ k)) = 0 := by
      intro i hi j hj hij ℓ hℓ p
      have hfree1 : ∀ nn : ℤ, (nn : ℂ) * τ k ∈ tripticPeriodGroup (τ j) (τ i) → nn = 0 := by
        intro nn hmem
        refine tripticPeriodGroup_free τ hQ (hneK i hi) (hneK j hj) nn ?_
        rw [zsmul_eq_mul]
        exact hmem
      have hs1 := finite_line_support_of_divFiniteClasses
        (hfin i (hmemS i hi) j (hmemS j hj) hij ℓ hℓ) hfree1 p
      have hs2 := finite_line_support_of_divFiniteClasses
        (divFiniteClasses_pairSig τ s hij (hmemS i hi) (hmemS j hj) hF₀mero hF₀per hF₀mixed
          (hτ j) hℓ) hfree1 p
      have hsplit : (∑ᶠ nn : ℤ, E i j ℓ (p + (nn : ℂ) * τ k))
          = (∑ᶠ nn : ℤ, D i j ℓ (p + (nn : ℂ) * τ k))
            - ∑ᶠ nn : ℤ, pairSig τ s F₀ i j ℓ (p + (nn : ℂ) * τ k) := by
        rw [hE]
        exact finsum_sub_distrib hs1 hs2
      rw [hsplit,
        htriple i (hmemS i hi) j (hmemS j hj) k hk hij (hneK i hi) (hneK j hj) ℓ hℓ p,
        pairSig_triple_compat τ hτ hQ s (hmemS i hi) (hmemS j hj) hk hij (hneK i hi) (hneK j hj)
          hF₀mero hF₀per hF₀mixed hℓ p]
      have hval : ∀ nn : ℤ, pairSig τ s F₀ i k ℓ (p + (nn : ℂ) * τ j)
          = D i k ℓ (p + (nn : ℂ) * τ j) := fun nn => hF₀sig i hi ℓ hℓ _
      rw [finsum_congr hval, sub_self]
    -- antidifference the error along `τ k`
    have hCex : ∀ (i j : ι) (ℓ : ℤ), ∃ C : ℂ → ℂ,
        (i ∈ s \ ({k} : Finset ι) → j ∈ s \ ({k} : Finset ι) → i ≠ j → ℓ < 0 →
          DivInvariant (tripticPeriodGroup (τ j) (τ i)) C ∧
            DivFiniteClasses (tripticPeriodGroup (τ j) (τ i)) C ∧
            ∀ p, C (p + τ k) - C p = E i j ℓ p) := by
      intro i j ℓ
      by_cases hcase : i ∈ s \ ({k} : Finset ι) ∧ j ∈ s \ ({k} : Finset ι) ∧ i ≠ j ∧ ℓ < 0
      · obtain ⟨hi, hj, hij, hℓ⟩ := hcase
        obtain ⟨C, hCinv, hCfin, hCstep⟩ := exists_antidifference_of_orbitSum_zero
          (H := tripticPeriodGroup (τ j) (τ i)) (t := -τ k) (D := E i j ℓ)
          (hEinv i hi j hj hij ℓ hℓ) (hEfin i hi j hj hij ℓ hℓ) (hkfree i hi j hj hij)
          (by
            intro p
            have hre : (∑ᶠ nn : ℤ, E i j ℓ (p + nn • (-τ k)))
                = ∑ᶠ nn : ℤ, E i j ℓ (p + (nn : ℂ) * τ k) := by
              have hterm : ∀ nn : ℤ, E i j ℓ (p + nn • (-τ k))
                  = (fun m : ℤ => E i j ℓ (p + (m : ℂ) * τ k)) (-nn) := by
                intro nn
                congr 1
                simp only [zsmul_eq_mul]
                push_cast
                ring
              rw [finsum_congr hterm]
              exact finsum_comp_equiv (Equiv.neg ℤ)
                (f := fun m : ℤ => E i j ℓ (p + (m : ℂ) * τ k))
            rw [hre]
            exact hEpush i hi j hj hij ℓ hℓ p)
        refine ⟨C, fun _ _ _ _ => ⟨hCinv, hCfin, ?_⟩⟩
        intro p
        have := hCstep (p + τ k)
        rw [show p + τ k - -τ k = p + τ k + τ k from by ring] at this
        have h2 := hCstep p
        rw [show p - -τ k = p + τ k from by ring] at h2
        exact h2
      · exact ⟨fun _ => 0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hcase⟩
    choose C hC using hCex
    have hCinvP : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → DivInvariant (tripticPeriodGroup (τ j) (τ i)) (C i j ℓ) :=
      fun i hi j hj hij ℓ hℓ => (hC i j ℓ hi hj hij hℓ).1
    have hCfinP : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → DivFiniteClasses (tripticPeriodGroup (τ j) (τ i)) (C i j ℓ) :=
      fun i hi j hj hij ℓ hℓ => (hC i j ℓ hi hj hij hℓ).2.1
    have hCstep : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → ∀ p, C i j ℓ (p + τ k) - C i j ℓ p = E i j ℓ p :=
      fun i hi j hj hij ℓ hℓ => (hC i j ℓ hi hj hij hℓ).2.2
    -- a uniform order bound
    have hMex : ∀ i j : ι, ∃ M : ℕ, i ∈ s → j ∈ s → i ≠ j →
        ∀ ℓ : ℤ, ℓ < -(M : ℤ) → ∀ p, pairSig τ s F₀ i j ℓ p = 0 := by
      intro i j
      by_cases hcase : i ∈ s ∧ j ∈ s ∧ i ≠ j
      · obtain ⟨hi, hj, hij⟩ := hcase
        obtain ⟨M, hM⟩ := exists_order_bound_pairSig τ s hij hi hj hF₀mero hF₀per hF₀mixed (hτ j)
        exact ⟨M, fun _ _ _ => hM⟩
      · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcase⟩
    choose M hM using hMex
    set N' : ℕ := max N (Finset.univ.sup fun q : ι × ι => M q.1 q.2) with hN'
    have hNle : (N : ℤ) ≤ (N' : ℤ) := by
      have : N ≤ N' := le_max_left _ _
      exact_mod_cast this
    have hMle : ∀ i j : ι, ((M i j : ℕ) : ℤ) ≤ (N' : ℤ) := by
      intro i j
      have h1 : M i j ≤ Finset.univ.sup fun q : ι × ι => M q.1 q.2 :=
        Finset.le_sup (f := fun q : ι × ι => M q.1 q.2) (Finset.mem_univ (i, j))
      have h2 : M i j ≤ N' := le_trans h1 (le_max_right _ _)
      exact_mod_cast h2
    have hEtop : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < -(N' : ℤ) → ∀ p, E i j ℓ p = 0 := by
      intro i hi j hj hij ℓ hℓ p
      have h1 : ℓ < -(N : ℤ) := lt_of_lt_of_le hℓ (by omega)
      have h2 : ℓ < -((M i j : ℕ) : ℤ) := lt_of_lt_of_le hℓ (by
        have := hMle i j
        omega)
      show D i j ℓ p - pairSig τ s F₀ i j ℓ p = 0
      rw [htop i (hmemS i hi) j (hmemS j hj) hij ℓ h1 p,
        hM i j (hmemS i hi) (hmemS j hj) hij ℓ h2 p, sub_self]
    have hCtop : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < -(N' : ℤ) → ∀ p, C i j ℓ p = 0 := by
      intro i hi j hj hij ℓ hℓ p
      have hℓ0 : ℓ < 0 := by
        have : (0 : ℤ) ≤ (N' : ℤ) := Int.natCast_nonneg _
        omega
      refine eq_zero_of_shiftDiff_eq_zero (H := tripticPeriodGroup (τ j) (τ i)) (t := -τ k)
        (hCfinP i hi j hj hij ℓ hℓ0) (hkfree i hi j hj hij) ?_ p
      intro q
      have h := hCstep i hi j hj hij ℓ hℓ0 q
      rw [show q - -τ k = q + τ k from by ring, h]
      exact hEtop i hi j hj hij ℓ hℓ q
    have hEsymm : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → E i j ℓ = E j i ℓ := by
      intro i hi j hj hij ℓ hℓ
      funext p
      show D i j ℓ p - pairSig τ s F₀ i j ℓ p = D j i ℓ p - pairSig τ s F₀ j i ℓ p
      rw [hsymm i (hmemS i hi) j (hmemS j hj) hij ℓ hℓ,
        pairSig_symm τ hτ hQ s hij (hmemS i hi) (hmemS j hj) hF₀mero hF₀per hF₀mixed hℓ p]
    have hCsymm : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
        ∀ ℓ : ℤ, ℓ < 0 → C i j ℓ = C j i ℓ := by
      intro i hi j hj hij ℓ hℓ
      funext p
      have hdiff : ∀ q : ℂ, (C i j ℓ q - C j i ℓ q) = 0 := by
        refine fun q => eq_zero_of_shiftDiff_eq_zero (H := tripticPeriodGroup (τ j) (τ i))
          (t := -τ k) (C := fun r => C i j ℓ r - C j i ℓ r)
          (DivFiniteClasses.sub (hCfinP i hi j hj hij ℓ hℓ)
            (by
              have h := hCfinP j hj i hi (Ne.symm hij) ℓ hℓ
              rwa [tripticPeriodGroup_comm] at h))
          (hkfree i hi j hj hij) ?_ q
        intro r
        have h1 := hCstep i hi j hj hij ℓ hℓ r
        have h2 := hCstep j hj i hi (Ne.symm hij) ℓ hℓ r
        show C i j ℓ (r - -τ k) - C j i ℓ (r - -τ k) - (C i j ℓ r - C j i ℓ r) = 0
        rw [show r - -τ k = r + τ k from by ring]
        have hEeq : E i j ℓ r = E j i ℓ r := by
          rw [hEsymm i hi j hj hij ℓ hℓ]
        linear_combination h1 - h2 + hEeq
      have := hdiff p
      linear_combination this
    -- triple compatibility of the antiderivatives
    have hCtriple : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι),
        ∀ l ∈ s \ ({k} : Finset ι), i ≠ j → i ≠ l → j ≠ l → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
        (∑ᶠ nn : ℤ, C i j ℓ (p + (nn : ℂ) * τ l))
          = ∑ᶠ nn : ℤ, C i l ℓ (p + (nn : ℂ) * τ j) := by
      intro i hi j hj l hl hij hil hjl ℓ hℓ p
      have hklm : k ∉ ({i, j, l} : Finset ι) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => (hneK i hi) h.symm, fun h => (hneK j hj) h.symm,
          fun h => (hneK l hl) h.symm⟩
      have hmemijl : ∀ u : ι, u ∈ ({i, j, l} : Finset ι) → True := fun _ _ => trivial
      have hifree : ∀ nn : ℤ, (nn : ℂ) * τ l ∈ tripticPeriodGroup (τ j) (τ i) → nn = 0 := by
        intro nn hmem
        refine tripticPeriodGroup_free τ hQ hil hjl nn ?_
        rw [zsmul_eq_mul]
        exact hmem
      have hjfree : ∀ nn : ℤ, (nn : ℂ) * τ j ∈ tripticPeriodGroup (τ l) (τ i) → nn = 0 := by
        intro nn hmem
        refine tripticPeriodGroup_free τ hQ hij (Ne.symm hjl) nn ?_
        rw [zsmul_eq_mul]
        exact hmem
      have hkfreeSpan : ∀ nn : ℤ, nn • τ k ∈ periodSpan τ ({i, j, l} : Finset ι) → nn = 0 := by
        intro nn hmem
        refine periodSpan_free τ hQ hklm nn ?_
        rwa [← zsmul_eq_mul]
      -- the two pushforwards differ by a `τ k`-invariant divisor with finitely many classes
      set X : ℂ → ℂ := fun q => ∑ᶠ nn : ℤ, C i j ℓ (q + (nn : ℂ) * τ l) with hX
      set Y : ℂ → ℂ := fun q => ∑ᶠ nn : ℤ, C i l ℓ (q + (nn : ℂ) * τ j) with hY
      have hXstep : ∀ q : ℂ, X (q + τ k) - X q
          = ∑ᶠ nn : ℤ, E i j ℓ (q + (nn : ℂ) * τ l) := by
        intro q
        have hfin1 := finite_line_support_of_divFiniteClasses
          (hCfinP i hi j hj hij ℓ hℓ) hifree (q + τ k)
        have hfin2 := finite_line_support_of_divFiniteClasses
          (hCfinP i hi j hj hij ℓ hℓ) hifree q
        have hterm : ∀ nn : ℤ, C i j ℓ (q + τ k + (nn : ℂ) * τ l)
            - C i j ℓ (q + (nn : ℂ) * τ l) = E i j ℓ (q + (nn : ℂ) * τ l) := by
          intro nn
          have h := hCstep i hi j hj hij ℓ hℓ (q + (nn : ℂ) * τ l)
          rw [show q + (nn : ℂ) * τ l + τ k = q + τ k + (nn : ℂ) * τ l from by ring] at h
          exact h
        rw [hX]
        show (∑ᶠ nn : ℤ, C i j ℓ (q + τ k + (nn : ℂ) * τ l))
          - ∑ᶠ nn : ℤ, C i j ℓ (q + (nn : ℂ) * τ l) = _
        rw [← finsum_sub_distrib hfin1 hfin2, finsum_congr hterm]
      have hYstep : ∀ q : ℂ, Y (q + τ k) - Y q
          = ∑ᶠ nn : ℤ, E i l ℓ (q + (nn : ℂ) * τ j) := by
        intro q
        have hfin1 := finite_line_support_of_divFiniteClasses
          (hCfinP i hi l hl hil ℓ hℓ) hjfree (q + τ k)
        have hfin2 := finite_line_support_of_divFiniteClasses
          (hCfinP i hi l hl hil ℓ hℓ) hjfree q
        have hterm : ∀ nn : ℤ, C i l ℓ (q + τ k + (nn : ℂ) * τ j)
            - C i l ℓ (q + (nn : ℂ) * τ j) = E i l ℓ (q + (nn : ℂ) * τ j) := by
          intro nn
          have h := hCstep i hi l hl hil ℓ hℓ (q + (nn : ℂ) * τ j)
          rw [show q + (nn : ℂ) * τ j + τ k = q + τ k + (nn : ℂ) * τ j from by ring] at h
          exact h
        rw [hY]
        show (∑ᶠ nn : ℤ, C i l ℓ (q + τ k + (nn : ℂ) * τ j))
          - ∑ᶠ nn : ℤ, C i l ℓ (q + (nn : ℂ) * τ j) = _
        rw [← finsum_sub_distrib hfin1 hfin2, finsum_congr hterm]
      have hEeq : ∀ q : ℂ, (∑ᶠ nn : ℤ, E i j ℓ (q + (nn : ℂ) * τ l))
          = ∑ᶠ nn : ℤ, E i l ℓ (q + (nn : ℂ) * τ j) := by
        intro q
        have hfinD1 := finite_line_support_of_divFiniteClasses
          (hfin i (hmemS i hi) j (hmemS j hj) hij ℓ hℓ) hifree q
        have hfinS1 := finite_line_support_of_divFiniteClasses
          (divFiniteClasses_pairSig τ s hij (hmemS i hi) (hmemS j hj) hF₀mero hF₀per hF₀mixed
            (hτ j) hℓ) hifree q
        have hfinD2 := finite_line_support_of_divFiniteClasses
          (hfin i (hmemS i hi) l (hmemS l hl) hil ℓ hℓ) hjfree q
        have hfinS2 := finite_line_support_of_divFiniteClasses
          (divFiniteClasses_pairSig τ s hil (hmemS i hi) (hmemS l hl) hF₀mero hF₀per hF₀mixed
            (hτ l) hℓ) hjfree q
        have hs1 : (∑ᶠ nn : ℤ, E i j ℓ (q + (nn : ℂ) * τ l))
            = (∑ᶠ nn : ℤ, D i j ℓ (q + (nn : ℂ) * τ l))
              - ∑ᶠ nn : ℤ, pairSig τ s F₀ i j ℓ (q + (nn : ℂ) * τ l) :=
          finsum_sub_distrib hfinD1 hfinS1
        have hs2 : (∑ᶠ nn : ℤ, E i l ℓ (q + (nn : ℂ) * τ j))
            = (∑ᶠ nn : ℤ, D i l ℓ (q + (nn : ℂ) * τ j))
              - ∑ᶠ nn : ℤ, pairSig τ s F₀ i l ℓ (q + (nn : ℂ) * τ j) :=
          finsum_sub_distrib hfinD2 hfinS2
        rw [hs1, hs2,
          htriple i (hmemS i hi) j (hmemS j hj) l (hmemS l hl) hij hil hjl ℓ hℓ q,
          pairSig_triple_compat τ hτ hQ s (hmemS i hi) (hmemS j hj) (hmemS l hl) hij hil hjl
            hF₀mero hF₀per hF₀mixed hℓ q]
      have hDeltainv : ∀ q : ℂ, (X - Y) (q + τ k) = (X - Y) q := by
        intro q
        show X (q + τ k) - Y (q + τ k) = X q - Y q
        have h1 := hXstep q
        have h2 := hYstep q
        have h3 := hEeq q
        linear_combination h1 - h2 + h3
      have hDeltafin : ∃ S : Finset ℂ, ∀ q, (X - Y) q ≠ 0 →
          ∃ r ∈ S, q - r ∈ periodSpan τ ({i, j, l} : Finset ι) := by
        obtain ⟨S₁, hS₁⟩ := hCfinP i hi j hj hij ℓ hℓ
        obtain ⟨S₂, hS₂⟩ := hCfinP i hi l hl hil ℓ hℓ
        refine ⟨S₁ ∪ S₂, fun q hq => ?_⟩
        by_cases hXq : X q = 0
        · have hYq : Y q ≠ 0 := by
            intro hcon
            exact hq (by show X q - Y q = 0; rw [hXq, hcon, sub_self])
          have hex : ∃ nn : ℤ, C i l ℓ (q + (nn : ℂ) * τ j) ≠ 0 := by
            by_contra hcon
            push Not at hcon
            exact hYq (by rw [hY]; show ∑ᶠ nn : ℤ, _ = 0; rw [finsum_congr hcon, finsum_zero])
          obtain ⟨nn, hnn⟩ := hex
          obtain ⟨r, hr, hmem⟩ := hS₂ _ hnn
          refine ⟨r, Finset.mem_union_right _ hr, ?_⟩
          have h1 : q + (nn : ℂ) * τ j - r ∈ periodSpan τ ({i, j, l} : Finset ι) :=
            tripticPeriodGroup_le_periodSpan τ (by simp) (by simp) hmem
          have h2 : ((-nn : ℤ) : ℂ) * τ j ∈ periodSpan τ ({i, j, l} : Finset ι) := by
            refine ⟨0, fun u => if u = j then -nn else 0, ?_⟩
            have hterm : ∀ u : ι, (((if u = j then -nn else 0 : ℤ)) : ℂ) * τ u
                = if u = j then ((-nn : ℤ) : ℂ) * τ u else 0 := by
              intro u
              split_ifs <;> push_cast <;> ring
            rw [Finset.sum_congr rfl fun u _ => hterm u,
              Finset.sum_ite_eq' ({i, j, l} : Finset ι) j (fun u => ((-nn : ℤ) : ℂ) * τ u),
              if_pos (by simp)]
            push_cast
            ring
          have h3 := add_mem h1 h2
          rw [show q + (nn : ℂ) * τ j - r + ((-nn : ℤ) : ℂ) * τ j = q - r from by push_cast; ring]
            at h3
          exact h3
        · have hex : ∃ nn : ℤ, C i j ℓ (q + (nn : ℂ) * τ l) ≠ 0 := by
            by_contra hcon
            push Not at hcon
            exact hXq (by rw [hX]; show ∑ᶠ nn : ℤ, _ = 0; rw [finsum_congr hcon, finsum_zero])
          obtain ⟨nn, hnn⟩ := hex
          obtain ⟨r, hr, hmem⟩ := hS₁ _ hnn
          refine ⟨r, Finset.mem_union_left _ hr, ?_⟩
          have h1 : q + (nn : ℂ) * τ l - r ∈ periodSpan τ ({i, j, l} : Finset ι) :=
            tripticPeriodGroup_le_periodSpan τ (by simp) (by simp) hmem
          have h2 : ((-nn : ℤ) : ℂ) * τ l ∈ periodSpan τ ({i, j, l} : Finset ι) := by
            refine ⟨0, fun u => if u = l then -nn else 0, ?_⟩
            have hterm : ∀ u : ι, (((if u = l then -nn else 0 : ℤ)) : ℂ) * τ u
                = if u = l then ((-nn : ℤ) : ℂ) * τ u else 0 := by
              intro u
              split_ifs <;> push_cast <;> ring
            rw [Finset.sum_congr rfl fun u _ => hterm u,
              Finset.sum_ite_eq' ({i, j, l} : Finset ι) l (fun u => ((-nn : ℤ) : ℂ) * τ u),
              if_pos (by simp)]
            push_cast
            ring
          have h3 := add_mem h1 h2
          rw [show q + (nn : ℂ) * τ l - r + ((-nn : ℤ) : ℂ) * τ l = q - r from by push_cast; ring]
            at h3
          exact h3
      obtain ⟨SΔ, hSΔ⟩ := hDeltafin
      have hzero := eq_zero_of_invariant_of_finite_classes (R := X - Y) (S := SΔ)
        (H := periodSpan τ ({i, j, l} : Finset ι)) hSΔ hkfreeSpan hDeltainv p
      have : X p - Y p = 0 := hzero
      linear_combination this
    -- the inductive hypothesis
    obtain ⟨F₁, Cst₁, hF₁mero, hF₁per, hF₁mixed, hF₁sig⟩ :=
      ih (n - 1) (by omega) (s \ ({k} : Finset ι)) hcard' (by omega) C hCinvP hCfinP
        ⟨N', hCtop⟩ hCsymm hCtriple
    have hF₁mixedS : MixedConstGermSet τ s F₁ 0 := mixedConstGermSet_of_erase τ s hk hF₁mixed
    refine ⟨fun z => F₀ z + F₁ z, Cst₀, ?_, ?_, ?_, ?_⟩
    · exact fun y _ => (hF₀mero y (Set.mem_univ y)).add (hF₁mero y (Set.mem_univ y))
    · exact periodicOneGerm_add hF₀per hF₁per
    · intro z
      filter_upwards [hF₀mixed z, hF₁mixedS z] with wv h1 h2
      have hsplit : HTGeometry.diffCube τ s (fun z => F₀ z + F₁ z) wv
          = HTGeometry.diffCube τ s F₀ wv + HTGeometry.diffCube τ s F₁ wv :=
        congrFun (HTGeometry.diffCube_add τ s F₀ F₁) wv
      rw [hsplit, h1, h2, add_zero]
    · intro i hi j hj hij ℓ hℓ p
      rw [pairSig_add τ hτ hQ s hij hi hj hF₀mero hF₀per hF₀mixed hF₁mero hF₁per hF₁mixedS hℓ p]
      by_cases hjk : j = k
      · subst hjk
        have hi' : i ∈ s \ ({j} : Finset ι) := Finset.mem_sdiff.mpr ⟨hi, by simpa using hij⟩
        rw [pairSig_eq_zero_of_mixedConstGermSet_erase τ s hij hi hF₁mero hF₁mixed hℓ p,
          hF₀sig i hi' ℓ hℓ p, add_zero]
      · by_cases hik : i = k
        · subst hik
          have hj' : j ∈ s \ ({i} : Finset ι) :=
            Finset.mem_sdiff.mpr ⟨hj, by simpa using (Ne.symm hij)⟩
          have hsym1 := pairSig_symm τ hτ hQ s hij hi hj hF₀mero hF₀per hF₀mixed hℓ p
          have hsym2 := pairSig_symm τ hτ hQ s hij hi hj hF₁mero hF₁per hF₁mixedS hℓ p
          rw [hsym1, hsym2,
            pairSig_eq_zero_of_mixedConstGermSet_erase τ s (Ne.symm hij) hj hF₁mero hF₁mixed hℓ p,
            hF₀sig j hj' ℓ hℓ p, add_zero,
            hsymm j hj i hi (Ne.symm hij) ℓ hℓ]
        · have hi' : i ∈ s \ ({k} : Finset ι) := Finset.mem_sdiff.mpr ⟨hi, by simpa using hik⟩
          have hj' : j ∈ s \ ({k} : Finset ι) := Finset.mem_sdiff.mpr ⟨hj, by simpa using hjk⟩
          rw [pairSig_descent τ hτ hQ s hik hjk hij hk hi hj hF₁mero hF₁per hF₁mixed hℓ p,
            hF₁sig i hi' j hj' hij ℓ hℓ (p + τ k), hF₁sig i hi' j hj' hij ℓ hℓ p,
            hCstep i hi' j hj' hij ℓ hℓ p]
          show pairSig τ s F₀ i j ℓ p + (D i j ℓ p - pairSig τ s F₀ i j ℓ p) = D i j ℓ p
          ring



end

end GaloisForLFunctions
