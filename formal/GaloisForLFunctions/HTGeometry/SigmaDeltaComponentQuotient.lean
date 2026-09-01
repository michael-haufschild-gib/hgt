import GaloisForLFunctions.HTGeometry.DifferentialPrimeComponentOrbit
import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotQuotient

/-!
# Simple domain components of a reduced difference-differential ring

For a finite intrinsic family of minimal differential primes in a `σ`-`δ`-simple ring, choose one
component and the least positive iterate stabilizing it.  The component quotient is a domain and is
simple for that iterate together with the induced derivation.  The proof uses irredundancy of the
minimal-prime intersection; no ordinary Noetherian hypothesis is introduced.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

variable {R : Type u} [CommRing R] [Differential R]

omit [Differential R] in
/-- Powers of a ring automorphism act by function iteration. -/
theorem ringEquiv_pow_apply (σ : R ≃+* R) (n : ℕ) (x : R) :
    (σ ^ n) x = σ^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change σ ((σ ^ n) x) = σ^[n + 1] x
      rw [ih, Function.iterate_succ_apply']

omit [Differential R] in
/-- Repeated ideal transport is transport by the corresponding automorphism power. -/
theorem ideal_map_pow_eq_iterate (σ : R ≃+* R) (P : Ideal R) (n : ℕ) :
    Ideal.map ((σ ^ n : R ≃+* R) : R →+* R) P =
      (fun Q : Ideal R => Ideal.map (σ : R →+* R) Q)^[n] P := by
  induction n with
  | zero =>
      change Ideal.map (RingHom.id R) P = P
      exact Ideal.map_id P
  | succ n ih =>
      rw [pow_succ', Function.iterate_succ_apply', ← ih, Ideal.map_map]
      rfl

/-- Every power of a derivation-commuting automorphism still commutes with the derivation. -/
theorem commutesDeriv_pow (σ : R ≃+* R) (hσ : CommutesDeriv σ) (n : ℕ) :
    CommutesDeriv (σ ^ n) := by
  intro x
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change σ ((σ ^ n) (Differential.deriv x)) =
        Differential.deriv (σ ((σ ^ n) x))
      rw [ih, hσ]

/-- The quotient by any chosen minimal differential-prime component is simple for the least
positive iterate stabilizing that component. -/
theorem exists_period_componentQuotient_isSigmaDeltaSimple
    [Nontrivial R] (σ : R ≃+* R) (hσ : CommutesDeriv σ)
    (hsimple : IsSigmaDeltaSimple σ)
    (S : Finset (Ideal R))
    (hSmin : ∀ P ∈ S, IsMinimalPrimeDifferentialIdeal P)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    (P : Ideal R) (hPS : P ∈ S) :
    ∃ (period : ℕ) (_ : 0 < period)
      (hPσ : IsSigmaIdeal (σ ^ period) P)
      (hPσsymm : IsSigmaIdeal (σ ^ period).symm P),
      letI : Differential (R ⧸ P) := quotientDifferential P (hSmin P hPS).2.1
      IsSigmaDeltaSimple
        (sigmaQuotientEquiv (σ ^ period) P hPσ hPσsymm) := by
  classical
  let F : Ideal R → Ideal R := fun J => Ideal.map (σ : R →+* R) J
  have hexPeriod : ∃ n, 0 < n ∧ F^[n] P = P :=
    exists_pos_iterate_map_eq_self_of_minimalPrimeDifferential σ hσ S hSmin hSbot hPS
  let period : ℕ := Nat.find hexPeriod
  have hperiodSpec : 0 < period ∧ F^[period] P = P := Nat.find_spec hexPeriod
  have hperiodPos : 0 < period := hperiodSpec.1
  have hperiod : Ideal.map (((σ ^ period) : R ≃+* R) : R →+* R) P = P := by
    rw [ideal_map_pow_eq_iterate]
    exact hperiodSpec.2
  have hperiodMinimal : ∀ i : ℕ, 0 < i → i < period → F^[i] P ≠ P := by
    intro i hiPos hiLt hiEq
    have hle := Nat.find_min' hexPeriod ⟨hiPos, hiEq⟩
    omega
  let τ : R ≃+* R := σ ^ period
  have hPσ : IsSigmaIdeal τ P := by
    intro x hx
    have hxmap := Ideal.mem_map_of_mem (τ : R →+* R) hx
    rwa [show Ideal.map (τ : R →+* R) P = P from hperiod] at hxmap
  have hmapSymm : Ideal.map (τ.symm : R →+* R) P = P := by
    have h := congrArg (fun J : Ideal R => Ideal.map (τ.symm : R →+* R) J) hperiod
    simpa [τ, Ideal.map_map] using h.symm
  have hPσsymm : IsSigmaIdeal τ.symm P := by
    intro x hx
    have hxmap := Ideal.mem_map_of_mem (τ.symm : R →+* R) hx
    rwa [hmapSymm] at hxmap
  refine ⟨period, hperiodPos, hPσ, hPσsymm, ?_⟩
  letI : Differential (R ⧸ P) := quotientDifferential P (hSmin P hPS).2.1
  intro J hJ
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  let I : Ideal R := Ideal.comap q J
  have hPI : P ≤ I := by
    intro x hx
    change q x ∈ J
    have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [hqx]
    exact J.zero_mem
  have hIσ : IsSigmaIdeal τ I := by
    intro x hx
    change q (τ x) ∈ J
    rw [← sigmaQuotientEquiv_mk τ P hPσ hPσsymm]
    exact hJ.1 (q x) hx
  have hIderiv : ∀ x ∈ I, Differential.deriv x ∈ I := by
    intro x hx
    change q (Differential.deriv x) ∈ J
    rw [← quotientDifferential_deriv_mk P (hSmin P hPS).2.1]
    exact hJ.2 (q x) hx
  have hJbot_of_Ieq (hIP : I = P) : J = ⊥ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxI : x ∈ I := hy
      have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIP ▸ hxI)
      exact Ideal.mem_bot.mpr hqx
    · exact bot_le
  by_cases hIP : I = P
  · exact Or.inl (hJbot_of_Ieq hIP)
  have hPIt : P < I := lt_of_le_of_ne hPI (Ne.symm hIP)
  have hnotIP : ¬ I ≤ P := not_le_of_gt hPIt
  have hb : ∃ b : R, b ∈ I ∧ b ∉ P := by
    rw [SetLike.le_def] at hnotIP
    push Not at hnotIP
    exact hnotIP
  obtain ⟨b, hbI, hbP⟩ := hb
  have hEraseNotLe : ¬ sInf ((S.erase P : Finset (Ideal R)) : Set (Ideal R)) ≤ P := by
    intro hle
    obtain ⟨Q, hQerase, hQP⟩ := exists_mem_le_of_sInf_le_isPrime (S.erase P)
      (hSmin P hPS).1 hle
    have hQS : Q ∈ S := Finset.mem_of_mem_erase hQerase
    have hPQ := (hSmin P hPS).2.2 Q (hSmin Q hQS).1 (hSmin Q hQS).2.1 hQP
    exact (Finset.ne_of_mem_erase hQerase) (le_antisymm hQP hPQ)
  have he : ∃ e : R,
      e ∈ sInf ((S.erase P : Finset (Ideal R)) : Set (Ideal R)) ∧ e ∉ P := by
    rw [SetLike.le_def] at hEraseNotLe
    push Not at hEraseNotLe
    exact hEraseNotLe
  obtain ⟨e, heOther, heP⟩ := he
  let c : R := b * e
  have hcI : c ∈ I := I.mul_mem_right e hbI
  have hcne : c ≠ 0 := by
    intro hc0
    have hcP : b * e ∈ P := by
      change b * e = 0 at hc0
      rw [hc0]
      exact P.zero_mem
    rcases (hSmin P hPS).1.mem_or_mem hcP with hbP' | heP'
    · exact hbP hbP'
    · exact heP heP'
  let orbitIdeals : Finset (Ideal R) :=
    (Finset.range period).image
      (fun i => Ideal.map (((σ ^ i) : R ≃+* R) : R →+* R) I)
  let H : Ideal R := sInf (orbitIdeals : Set (Ideal R))
  have hmapZero (J : Ideal R) :
      Ideal.map ((((σ ^ 0) : R ≃+* R)) : R →+* R) J = J := by
    change Ideal.map (RingHom.id R) J = J
    exact Ideal.map_id J
  have hiterMinAll : ∀ i : ℕ, IsMinimalPrimeDifferentialIdeal (F^[i] P) := by
    intro i
    induction i with
    | zero => simpa using hSmin P hPS
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact ih.map_ringEquiv σ hσ
  have horbitP (i : ℕ) (hi : i < period) :
      Ideal.map (((σ ^ i) : R ≃+* R) : R →+* R) P ∈ S := by
    have hmin : IsMinimalPrimeDifferentialIdeal
        (Ideal.map (((σ ^ i) : R ≃+* R) : R →+* R) P) := by
      rw [ideal_map_pow_eq_iterate]
      exact hiterMinAll i
    exact mem_finite_minimalPrimeDifferential_family S hSmin hSbot hmin
  have hcOrbit : c ∈ H := by
    have hspan : Ideal.span {c} ≤ H := by
      dsimp [H]
      apply le_sInf
      intro Q hQorbit
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQorbit
      have hiPeriod : i < period := Finset.mem_range.mp hi
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      by_cases hi0 : i = 0
      · subst i
        rw [hmapZero]
        exact hcI
      · have hPiS := horbitP i hiPeriod
        have hPiNe : Ideal.map (((σ ^ i) : R ≃+* R) : R →+* R) P ≠ P := by
          rw [ideal_map_pow_eq_iterate]
          exact hperiodMinimal i (Nat.pos_of_ne_zero hi0) hiPeriod
        have hPiErase : Ideal.map (((σ ^ i) : R ≃+* R) : R →+* R) P ∈ S.erase P :=
          Finset.mem_erase.mpr ⟨hPiNe, hPiS⟩
        have hePi := (sInf_le hPiErase) heOther
        change b * e ∈ Ideal.map (((σ ^ i) : R ≃+* R) : R →+* R) I
        exact Ideal.mul_mem_left _ b
          ((Ideal.map_mono (f := (((σ ^ i) : R ≃+* R) : R →+* R)) hPI) hePi)
    exact hspan (Ideal.mem_span_singleton_self c)
  have hHneBot : H ≠ ⊥ := by
    intro hHbot
    exact hcne (Ideal.mem_bot.mp (hHbot ▸ hcOrbit))
  have hHleI : H ≤ I := by
    have h0 : I ∈ orbitIdeals := by
      dsimp [orbitIdeals]
      apply Finset.mem_image.mpr
      refine ⟨0, Finset.mem_range.mpr hperiodPos, ?_⟩
      exact hmapZero I
    exact sInf_le h0
  have hHstable : IsSigmaDeltaIdeal σ H := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxOrbit : ∀ i : ℕ, i < period →
          x ∈ Ideal.map ((((σ ^ i) : R ≃+* R)) : R →+* R) I := by
        intro i hi
        apply (show H ≤ Ideal.map ((((σ ^ i) : R ≃+* R)) : R →+* R) I from ?_) hx
        dsimp [H, orbitIdeals]
        exact sInf_le (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
      have hspan : Ideal.span {σ x} ≤ H := by
        dsimp [H]
        apply le_sInf
        intro Q hQorbit
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQorbit
        have hiPeriod : i < period := Finset.mem_range.mp hi
        rw [Ideal.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        cases i with
        | zero =>
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hperiodPos)
            have hxk : x ∈ Ideal.map ((((σ ^ k) : R ≃+* R)) : R →+* R) I :=
              hxOrbit k (by omega)
            obtain ⟨a, haI, haEq⟩ :=
              (Ideal.mem_map_iff_of_surjective
                ((((σ ^ k) : R ≃+* R)) : R →+* R) (σ ^ k).surjective).mp hxk
            have hτa : τ a ∈ I := hIσ a haI
            rw [hmapZero]
            have heq : τ a = σ x := by
              rw [show τ = σ ^ (k + 1) by simp only [τ, hk], pow_succ']
              change σ ((σ ^ k) a) = σ x
              exact congrArg σ haEq
            rwa [← heq]
        | succ i =>
            have hxi : x ∈ Ideal.map ((((σ ^ i) : R ≃+* R)) : R →+* R) I :=
              hxOrbit i (by omega)
            obtain ⟨a, haI, haEq⟩ :=
              (Ideal.mem_map_iff_of_surjective
                ((((σ ^ i) : R ≃+* R)) : R →+* R) (σ ^ i).surjective).mp hxi
            have hout := Ideal.mem_map_of_mem
              ((((σ ^ (i + 1)) : R ≃+* R)) : R →+* R) haI
            have heq : (σ ^ (i + 1)) a = σ x := by
              rw [pow_succ']
              change σ ((σ ^ i) a) = σ x
              exact congrArg σ haEq
            rw [← heq]
            exact hout
      exact hspan (Ideal.mem_span_singleton_self (σ x))
    · intro x hx
      have hxOrbit : ∀ i : ℕ, i < period →
          x ∈ Ideal.map ((((σ ^ i) : R ≃+* R)) : R →+* R) I := by
        intro i hi
        apply (show H ≤ Ideal.map ((((σ ^ i) : R ≃+* R)) : R →+* R) I from ?_) hx
        dsimp [H, orbitIdeals]
        exact sInf_le (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
      have hspan : Ideal.span {Differential.deriv x} ≤ H := by
        dsimp [H]
        apply le_sInf
        intro Q hQorbit
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQorbit
        rw [Ideal.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have hxi : x ∈ Ideal.map ((((σ ^ i) : R ≃+* R)) : R →+* R) I :=
          hxOrbit i (Finset.mem_range.mp hi)
        obtain ⟨a, haI, haEq⟩ :=
          (Ideal.mem_map_iff_of_surjective
            ((((σ ^ i) : R ≃+* R)) : R →+* R) (σ ^ i).surjective).mp hxi
        have hda := Ideal.mem_map_of_mem
          ((((σ ^ i) : R ≃+* R)) : R →+* R) (hIderiv a haI)
        have heq : Differential.deriv x = (σ ^ i) (Differential.deriv a) := by
          rw [← haEq]
          exact (commutesDeriv_pow σ hσ i a).symm
        rw [heq]
        exact hda
      exact hspan (Ideal.mem_span_singleton_self (Differential.deriv x))
  have hHeqTop : H = ⊤ := (hsimple H hHstable).resolve_left hHneBot
  have hIeqTop : I = ⊤ := top_unique (hHeqTop ▸ hHleI)
  refine Or.inr ?_
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hxI : x ∈ I := by rw [hIeqTop]; trivial
  exact hxI

/-- At least one minimal differential-prime component quotient is simple for a positive iterate
of the difference automorphism. -/
theorem exists_componentQuotient_isSigmaDeltaSimple
    [Nontrivial R] (σ : R ≃+* R) (hσ : CommutesDeriv σ)
    (hsimple : IsSigmaDeltaSimple σ)
    (S : Finset (Ideal R)) (hSne : S.Nonempty)
    (hSmin : ∀ P ∈ S, IsMinimalPrimeDifferentialIdeal P)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥) :
    ∃ (P : Ideal R) (period : ℕ) (_ : 0 < period) (hPS : P ∈ S)
      (hPσ : IsSigmaIdeal (σ ^ period) P)
      (hPσsymm : IsSigmaIdeal (σ ^ period).symm P),
      letI : Differential (R ⧸ P) := quotientDifferential P (hSmin P hPS).2.1
      IsSigmaDeltaSimple
        (sigmaQuotientEquiv (σ ^ period) P hPσ hPσsymm) := by
  obtain ⟨P, hPS⟩ := hSne
  obtain ⟨period, hperiodPos, hPσ, hPσsymm, hsimpleP⟩ :=
    exists_period_componentQuotient_isSigmaDeltaSimple
      σ hσ hsimple S hSmin hSbot P hPS
  exact ⟨P, period, hperiodPos, hPS, hPσ, hPσsymm, hsimpleP⟩

end

end GaloisForLFunctions.HTGeometry
