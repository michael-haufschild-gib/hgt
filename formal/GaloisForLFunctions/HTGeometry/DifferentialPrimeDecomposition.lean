import GaloisForLFunctions.HTGeometry.KolchinNoetherianFinitelyMany
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealPrime
import GaloisForLFunctions.HTGeometry.RadDiffFGTransfer

/-!
# Finite differential-prime decomposition

Ritt--Raudenbush ACC turns the standard prime-splitting argument into a finite decomposition:
every radical differential ideal in finitely many differential indeterminates is an intersection
of finitely many prime differential ideals.  This is the component theorem needed for reduced
parameterized Picard--Vessiot rings; no ordinary Noetherian hypothesis is available because their
coordinate rings contain jets of every order.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

universe u

/-- A radical ideal stable under the distinguished derivation. -/
def IsRadicalDifferentialIdeal {R : Type*} [CommRing R] [Differential R]
    (I : Ideal R) : Prop :=
  I.IsRadical ∧ ∀ x ∈ I, Differential.deriv x ∈ I

/-- A finite intersection presentation by differential prime ideals. -/
def HasFinitePrimeDifferentialDecomposition {R : Type*} [CommRing R] [Differential R]
    (I : Ideal R) : Prop :=
  ∃ S : Finset (Ideal R),
    (∀ P ∈ S, P.IsPrime ∧ ∀ x ∈ P, Differential.deriv x ∈ P) ∧
      I = sInf (S : Set (Ideal R))

/-- A differential prime minimal among all differential prime ideals. -/
def IsMinimalPrimeDifferentialIdeal {R : Type*} [CommRing R] [Differential R]
    (P : Ideal R) : Prop :=
  P.IsPrime ∧ (∀ x ∈ P, Differential.deriv x ∈ P) ∧
    ∀ Q : Ideal R, Q.IsPrime → (∀ x ∈ Q, Differential.deriv x ∈ Q) →
      Q ≤ P → P ≤ Q

/-- If a finite ideal intersection lies in a prime, one of its factors lies in that prime. -/
theorem exists_mem_le_of_sInf_le_isPrime {R : Type*} [CommRing R]
    (S : Finset (Ideal R)) {P : Ideal R} (hP : P.IsPrime)
    (hSP : sInf (S : Set (Ideal R)) ≤ P) :
    ∃ Q ∈ S, Q ≤ P := by
  classical
  by_contra hnone
  push Not at hnone
  have hchoose : ∀ Q ∈ S, ∃ x : R, x ∈ Q ∧ x ∉ P := by
    intro Q hQS
    have hnot := hnone Q hQS
    rw [SetLike.le_def] at hnot
    push Not at hnot
    exact hnot
  let x : Ideal R → R := fun Q =>
    if hQS : Q ∈ S then Classical.choose (hchoose Q hQS) else 0
  have hxQ : ∀ Q ∈ S, x Q ∈ Q := by
    intro Q hQS
    simp only [x, dif_pos hQS]
    exact (Classical.choose_spec (hchoose Q hQS)).1
  have hxP : ∀ Q ∈ S, x Q ∉ P := by
    intro Q hQS
    simp only [x, dif_pos hQS]
    exact (Classical.choose_spec (hchoose Q hQS)).2
  let z : R := ∏ Q ∈ S, x Q
  have hzS : z ∈ sInf (S : Set (Ideal R)) := by
    have hspan : Ideal.span {z} ≤ sInf (S : Set (Ideal R)) := by
      apply le_sInf
      intro Q hQS
      rw [Ideal.span_le]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      rw [show z = x Q * ∏ T ∈ S \ {Q}, x T by
        simpa [z] using Finset.prod_eq_mul_prod_sdiff_singleton Q x
          (fun hQnot => (hQnot hQS).elim)]
      exact Q.mul_mem_right _ (hxQ Q hQS)
    exact hspan (Ideal.mem_span_singleton_self z)
  have hzP : z ∈ P := hSP hzS
  have hprimeProd : ∀ T : Finset (Ideal R),
      (∏ Q ∈ T, x Q) ∈ P → ∃ Q ∈ T, x Q ∈ P := by
    intro T
    induction T using Finset.induction with
    | empty =>
        intro hOne
        exact (hP.ne_top ((Ideal.eq_top_iff_one P).2 hOne)).elim
    | @insert Q T hQT ih =>
        intro hprod
        rw [Finset.prod_insert hQT] at hprod
        rcases hP.mem_or_mem hprod with hQ | hT
        · exact ⟨Q, Finset.mem_insert_self Q T, hQ⟩
        · obtain ⟨U, hUT, hU⟩ := ih hT
          exact ⟨U, Finset.mem_insert_of_mem hUT, hU⟩
  obtain ⟨Q, hQS, hQ⟩ := hprimeProd S hzP
  exact hxP Q hQS hQ

private theorem exists_maximal_of_monotone_chain_stabilizes
    {A : Type*} [PartialOrder A] (P : A → Prop) (a₀ : A) (ha₀ : P a₀)
    (hacc : ∀ f : ℕ → A, Monotone f → (∀ n, P (f n)) →
      ∃ N : ℕ, ∀ n, N ≤ n → f n = f N) :
    ∃ a : A, P a ∧ ∀ b : A, P b → a ≤ b → b = a := by
  classical
  by_contra hmax
  push Not at hmax
  let B := {a : A // P a}
  have hnext : ∀ a : B, ∃ b : B, a.1 < b.1 := by
    intro a
    obtain ⟨b, hbP, hab, hba⟩ := hmax a.1 a.2
    exact ⟨⟨b, hbP⟩, lt_of_le_of_ne hab (Ne.symm hba)⟩
  choose step hstep using hnext
  let fB : ℕ → B := fun n => Nat.rec ⟨a₀, ha₀⟩ (fun _ a => step a) n
  let f : ℕ → A := fun n => (fB n).1
  have hf_succ (n : ℕ) : f (n + 1) = (step (fB n)).1 := by
    simp [f, fB]
  have hf_strict (n : ℕ) : f n < f (n + 1) := by
    rw [hf_succ]
    exact hstep (fB n)
  have hfmono : Monotone f := monotone_nat_of_le_succ fun n => (hf_strict n).le
  obtain ⟨N, hN⟩ := hacc f hfmono (fun n => (fB n).2)
  exact (hf_strict N).ne (hN (N + 1) (Nat.le_succ N)).symm

variable {K : Type u} [Field K] [Algebra ℚ K] [Differential K]

/-- **Finite differential-prime decomposition.**  Every radical differential ideal in finitely
many differential variables is a finite intersection of derivation-stable prime ideals. -/
theorem exists_finite_primeDifferential_decomposition {n : ℕ}
    (I : Ideal (DifferentialPolynomial (Fin n) K))
    (hIrad : I.IsRadical) (hIderiv : ∀ x ∈ I, Differential.deriv x ∈ I) :
    HasFinitePrimeDifferentialDecomposition I := by
  classical
  by_contra hIdec
  let Bad : Ideal (DifferentialPolynomial (Fin n) K) → Prop := fun J =>
    IsRadicalDifferentialIdeal J ∧ ¬ HasFinitePrimeDifferentialDecomposition J
  have hbadI : Bad I := ⟨⟨hIrad, hIderiv⟩, hIdec⟩
  have hacc : ∀ f : ℕ → Ideal (DifferentialPolynomial (Fin n) K), Monotone f →
      (∀ m, Bad (f m)) → ∃ N : ℕ, ∀ m, N ≤ m → f m = f N := by
    intro f hf hfbad
    exact acc_radicalDifferentialIdeal_fin n f hf
      (fun m => (hfbad m).1.1) (fun m => (hfbad m).1.2)
  obtain ⟨M, hMbad, hMmax⟩ :=
    exists_maximal_of_monotone_chain_stabilizes Bad I hbadI
      hacc
  have hMtop : M ≠ ⊤ := by
    intro htop
    apply hMbad.2
    refine ⟨∅, ?_, ?_⟩
    · simp
    · simp [htop]
  have hMnotprime : ¬ M.IsPrime := by
    intro hprime
    apply hMbad.2
    refine ⟨{M}, ?_, ?_⟩
    · intro P hP
      simp only [Finset.mem_singleton] at hP
      subst P
      exact ⟨hprime, hMbad.1.2⟩
    · simp
  rw [Ideal.isPrime_iff] at hMnotprime
  push Not at hMnotprime
  obtain ⟨a, b, hab, ha, hb⟩ := hMnotprime hMtop
  let A := radicalDifferentialIdeal ((M : Set _) ∪ {a})
  let B := radicalDifferentialIdeal ((M : Set _) ∪ {b})
  have hMA : M ≤ A := fun x hx => subset_radicalDifferentialIdeal _ (Or.inl hx)
  have hMB : M ≤ B := fun x hx => subset_radicalDifferentialIdeal _ (Or.inl hx)
  have haA : a ∈ A := subset_radicalDifferentialIdeal _ (Or.inr rfl)
  have hbB : b ∈ B := subset_radicalDifferentialIdeal _ (Or.inr rfl)
  have hltA : M < A := lt_of_le_of_ne hMA (fun h => ha (h ▸ haA))
  have hltB : M < B := lt_of_le_of_ne hMB (fun h => hb (h ▸ hbB))
  have hAbadOrDec : HasFinitePrimeDifferentialDecomposition A := by
    by_contra hAdec
    exact hltA.ne' (hMmax A
      ⟨⟨isRadical_radicalDifferentialIdeal _, deriv_mem_radicalDifferentialIdeal _⟩,
        hAdec⟩ hMA)
  have hBbadOrDec : HasFinitePrimeDifferentialDecomposition B := by
    by_contra hBdec
    exact hltB.ne' (hMmax B
      ⟨⟨isRadical_radicalDifferentialIdeal _, deriv_mem_radicalDifferentialIdeal _⟩,
        hBdec⟩ hMB)
  obtain ⟨SA, hSAprime, hSA⟩ := hAbadOrDec
  obtain ⟨SB, hSBprime, hSB⟩ := hBbadOrDec
  have hpair : ∀ s ∈ ((M : Set _) ∪ {a}), ∀ t ∈ ((M : Set _) ∪ {b}),
      s * t ∈ M := by
    rintro s (hs | rfl) t (ht | rfl)
    · exact M.mul_mem_right _ hs
    · exact M.mul_mem_right _ hs
    · exact M.mul_mem_left _ ht
    · exact hab
  have hM_inf : M = A ⊓ B := by
    apply le_antisymm
    · exact le_inf hMA hMB
    · intro x hx
      exact hMbad.1.1 ⟨2, by
        rw [pow_two]
        exact mul_mem_of_forall_mul_mem hMbad.1.1 hMbad.1.2 hpair hx.1 hx.2⟩
  apply hMbad.2
  refine ⟨SA ∪ SB, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hSAprime P hP
    · exact hSBprime P hP
  · rw [Finset.coe_union, sInf_union, ← hSA, ← hSB, hM_inf]

/-- A reduced differentially finitely generated algebra has finitely many differential-prime
components with zero intersection. -/
theorem exists_finite_primeDifferential_inf_eq_bot_of_diffFG
    {R : Type u} [CommRing R] [Nontrivial R] [IsReduced R]
    [Algebra K R] [Differential R] [DifferentialAlgebra K R]
    {n : ℕ} (y : Fin n → R)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := K) (L := R) y)) :
    ∃ S : Finset (Ideal R), S.Nonempty ∧
      (∀ P ∈ S, P.IsPrime ∧ ∀ x ∈ P, Differential.deriv x ∈ P) ∧
      sInf (S : Set (Ideal R)) = ⊥ := by
  classical
  let f : DifferentialPolynomial (Fin n) K →+* R :=
    (differentialPolynomialEvalOver (K := K) y).toRingHom
  let J : Ideal (DifferentialPolynomial (Fin n) K) := RingHom.ker f
  have hJrad : J.IsRadical := by
    intro Q hQ
    obtain ⟨m, hm⟩ := hQ
    change f Q = 0
    apply IsReduced.eq_zero
    refine ⟨m, ?_⟩
    rw [← map_pow]
    exact hm
  have hfderiv (Q : DifferentialPolynomial (Fin n) K) :
      f (Differential.deriv Q) = Differential.deriv (f Q) := by
    exact differentialPolynomialEvalOver_derivation y Q
  have hJderiv : ∀ Q ∈ J, Differential.deriv Q ∈ J := by
    intro Q hQ
    change f (Differential.deriv Q) = 0
    rw [hfderiv, show f Q = 0 from hQ, map_zero]
  obtain ⟨S, hSprime, hSJ⟩ :=
    exists_finite_primeDifferential_decomposition J hJrad hJderiv
  let T : Finset (Ideal R) := S.image (fun P => Ideal.map f P)
  have hker_le (P : Ideal (DifferentialPolynomial (Fin n) K)) (hP : P ∈ S) :
      RingHom.ker f ≤ P := by
    rw [show RingHom.ker f = J by rfl, hSJ]
    exact sInf_le hP
  have hTprime : ∀ Q ∈ T,
      Q.IsPrime ∧ ∀ x ∈ Q, Differential.deriv x ∈ Q := by
    intro Q hQ
    obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hQ
    letI : P.IsPrime := (hSprime P hPS).1
    exact ⟨Ideal.map_isPrime_of_surjective hy (hker_le P hPS),
      deriv_mem_map_of_surjective f hfderiv hy (hSprime P hPS).2⟩
  have hTbot : sInf (T : Set (Ideal R)) = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨q, hqx⟩ := hy x
      have hqJ : q ∈ J := by
        rw [hSJ]
        have hspan : Ideal.span {q} ≤ sInf (S : Set (Ideal _)) := by
          apply le_sInf
          intro P hPS
          rw [Ideal.span_le]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          have hxmap : x ∈ Ideal.map f P := by
            apply (sInf_le (show Ideal.map f P ∈ (T : Set (Ideal R)) by
              exact_mod_cast Finset.mem_image_of_mem (fun Q => Ideal.map f Q) hPS))
            exact hx
          obtain ⟨qP, hqPP, hqPx⟩ :=
            (Ideal.mem_map_iff_of_surjective f hy).mp hxmap
          have hdiff : q - qP ∈ RingHom.ker f := by
            change f (q - qP) = 0
            change f q = x at hqx
            rw [map_sub, hqx, hqPx, sub_self]
          rw [show q = (q - qP) + qP by abel]
          exact P.add_mem (hker_le P hPS hdiff) hqPP
        exact hspan (Ideal.mem_span_singleton_self q)
      have : x = 0 := by
        rw [← hqx]
        exact hqJ
      exact Ideal.mem_bot.mpr this
    · exact bot_le
  have hTne : T.Nonempty := by
    by_contra hTempty
    rw [Finset.not_nonempty_iff_eq_empty] at hTempty
    simp only [hTempty, Finset.coe_empty, sInf_empty] at hTbot
    have htopbot : (⊤ : Ideal R) = ⊥ := hTbot
    exact (one_ne_zero : (1 : R) ≠ 0) (by
      have h1 : (1 : R) ∈ (⊥ : Ideal R) := by rw [← htopbot]; trivial
      exact Ideal.mem_bot.mp h1)
  exact ⟨T, hTne, hTprime, hTbot⟩

/-- The finite component family can be chosen to be exactly differential-prime-minimal: its
members are globally minimal differential primes, hence pairwise incomparable and intrinsic. -/
theorem exists_finite_minimalPrimeDifferential_inf_eq_bot_of_diffFG
    {R : Type u} [CommRing R] [Nontrivial R] [IsReduced R]
    [Algebra K R] [Differential R] [DifferentialAlgebra K R]
    {n : ℕ} (y : Fin n → R)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := K) (L := R) y)) :
    ∃ S : Finset (Ideal R), S.Nonempty ∧
      (∀ P ∈ S, IsMinimalPrimeDifferentialIdeal P) ∧
      sInf (S : Set (Ideal R)) = ⊥ := by
  classical
  obtain ⟨S, hSne, hSprime, hSbot⟩ :=
    exists_finite_primeDifferential_inf_eq_bot_of_diffFG y hy
  let T : Finset (Ideal R) :=
    S.filter (fun P => Minimal (fun Q : Ideal R => Q ∈ S) P)
  have hcover : ∀ P ∈ S, ∃ Q ∈ T, Q ≤ P := by
    intro P hPS
    let U : Finset (Ideal R) := S.filter (fun Q => Q ≤ P)
    have hUne : U.Nonempty := ⟨P, Finset.mem_filter.mpr ⟨hPS, le_rfl⟩⟩
    obtain ⟨Q, hQmin⟩ := Finset.exists_minimal hUne
    have hQU : Q ∈ U := hQmin.1
    have hQS : Q ∈ S := (Finset.mem_filter.mp hQU).1
    have hQP : Q ≤ P := (Finset.mem_filter.mp hQU).2
    have hQminS : Minimal (fun V : Ideal R => V ∈ S) Q := by
      refine ⟨hQS, ?_⟩
      intro V hVS hVQ
      have hVU : V ∈ U := Finset.mem_filter.mpr ⟨hVS, le_trans hVQ hQP⟩
      exact hQmin.2 hVU hVQ
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQS, hQminS⟩, hQP⟩
  have hTne : T.Nonempty := by
    obtain ⟨P, hPS⟩ := hSne
    obtain ⟨Q, hQT, -⟩ := hcover P hPS
    exact ⟨Q, hQT⟩
  have hTminimal : ∀ P ∈ T, IsMinimalPrimeDifferentialIdeal P := by
    intro P hPT
    obtain ⟨hPS, hPminS⟩ := Finset.mem_filter.mp hPT
    refine ⟨(hSprime P hPS).1, (hSprime P hPS).2, ?_⟩
    intro Q hQprime hQderiv hQP
    obtain ⟨U, hUS, hUQ⟩ :=
      exists_mem_le_of_sInf_le_isPrime S hQprime
        (le_trans (show sInf (S : Set (Ideal R)) = ⊥ from hSbot).le bot_le)
    exact le_trans (hPminS.2 hUS (le_trans hUQ hQP)) hUQ
  have hTbot : sInf (T : Set (Ideal R)) = ⊥ := by
    apply le_antisymm
    · rw [← hSbot]
      apply le_sInf
      intro P hPS
      obtain ⟨Q, hQT, hQP⟩ := hcover P hPS
      exact le_trans (sInf_le hQT) hQP
    · exact bot_le
  exact ⟨T, hTne, hTminimal, hTbot⟩

end

end GaloisForLFunctions.HTGeometry
