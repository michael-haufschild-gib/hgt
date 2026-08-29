import Mathlib

/-!
# Bass's stable range theorem for Dedekind domains

A Dedekind domain has stable range at most two: a unimodular triple `(a, b, c)` can be shortened —
`(a + xc, b + yc)` is unimodular for suitable `x, y`.  This is the input that replaces
"a primitive vector extends to a basis" — true over a principal ideal domain, false over a general
Dedekind domain — in the covering half of Siegel reduction over a ring of integers.

The proof is elementary once the right choice is made.  If `b = 0` the pair `(a, c)` is already
unimodular, so `x = 0`, `y = 1` works.  Otherwise only finitely many maximal ideals contain `b`
(`Ideal.finite_factors`), and the Chinese remainder theorem chooses one `x` handling all of them at
once: where `c` lies in the maximal ideal `a` cannot, by unimodularity, so nothing is required
there; where `c` does not, `c` is invertible modulo it and `x` is chosen to make `a + xc ≡ 1`.

* `exists_stableRange_two` — the shortening, in Bézout form.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain

/-- **Stable range two for a Dedekind domain.** -/
theorem exists_stableRange_two {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a b c : R} (h : ∃ u v w : R, u * a + v * b + w * c = 1) :
    ∃ x y p q : R, p * (a + x * c) + q * (b + y * c) = 1 := by
  classical
  obtain ⟨u, v, w, huvw⟩ := h
  by_cases hb : b = 0
  · subst hb
    refine ⟨0, 1, u, w, ?_⟩
    linear_combination huvw
  -- the finitely many maximal ideals containing `b`
  have hbspan : (Ideal.span {b} : Ideal R) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hb
  have hfin : {t : HeightOneSpectrum R | t.asIdeal ∣ Ideal.span {b}}.Finite :=
    Ideal.finite_factors hbspan
  -- the residue prescription at each height-one point
  have hz : ∀ t : HeightOneSpectrum R, ∃ z : R,
      c ∉ t.asIdeal → a + z * c - 1 ∈ t.asIdeal := by
    intro t
    by_cases hct : c ∈ t.asIdeal
    · exact ⟨0, fun hcon => absurd hct hcon⟩
    · obtain ⟨d, i, hi, hdi⟩ := t.isMaximal.exists_inv hct
      refine ⟨(1 - a) * d, fun _ => ?_⟩
      have hkey : a + (1 - a) * d * c - 1 = -((1 - a) * i) := by linear_combination (1 - a) * hdi
      rw [hkey]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hi)
  choose z hzspec using hz
  -- one `x` by the Chinese remainder theorem
  have hcop : Pairwise (Function.onFun IsCoprime
      (fun t : hfin.toFinset => (t : HeightOneSpectrum R).asIdeal)) := by
    intro s t hst
    have hne : (s : HeightOneSpectrum R).asIdeal ≠ (t : HeightOneSpectrum R).asIdeal := by
      intro hEq
      exact hst (Subtype.ext (HeightOneSpectrum.ext hEq))
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (HeightOneSpectrum.isMaximal _)
      (HeightOneSpectrum.isMaximal _) hne
  obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun t : hfin.toFinset => z (t : HeightOneSpectrum R))
  refine ⟨x, 0, ?_⟩
  -- the shortened pair is unimodular
  by_contra hcon
  push Not at hcon
  have htop : Ideal.span {a + x * c, b + 0 * c} ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one, Submodule.mem_span_pair] at htop
    obtain ⟨p, q, hpq⟩ := htop
    exact hcon p q (by simpa [smul_eq_mul] using hpq)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ htop
  have hA : a + x * c ∈ m := hle (Ideal.subset_span (by simp))
  have hB : b ∈ m := by
    have := hle (Ideal.subset_span (show b + 0 * c ∈ ({a + x * c, b + 0 * c} : Set R) by simp))
    simpa using this
  have hmne : m ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hB
    exact hb hB
  set t : HeightOneSpectrum R := ⟨m, hm.isPrime, hmne⟩ with ht
  have htS : t ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show t.asIdeal ∣ Ideal.span {b}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hB
  have hone : (1 : R) ∈ m := by
    by_cases hct : c ∈ m
    · have ha : a ∈ m := by
        have : a = (a + x * c) - x * c := by ring
        rw [this]
        exact Ideal.sub_mem _ hA (Ideal.mul_mem_left _ _ hct)
      have : (1 : R) = u * a + v * b + w * c := huvw.symm
      rw [this]
      exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
        (Ideal.mul_mem_left _ _ hB)) (Ideal.mul_mem_left _ _ hct)
    · have h1 : a + z t * c - 1 ∈ m := hzspec t hct
      have h2 : x - z t ∈ m := hx ⟨t, htS⟩
      have h3 : a + x * c - 1 = (a + z t * c - 1) + (x - z t) * c := by ring
      have h4 : a + x * c - 1 ∈ m := by
        rw [h3]
        exact Ideal.add_mem _ h1 (Ideal.mul_mem_right _ _ h2)
      have : (1 : R) = (a + x * c) - (a + x * c - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ hA h4
  exact hm.ne_top (Ideal.eq_top_iff_one m |>.mpr hone)

/-- **Vaserstein's lemma**: stable range two propagates to every length.  The grouping that works
puts the *whole tail* into the auxiliary coordinate: with `d = u_last · a_last + w · c`, the shorter
vector `(a₁, …, a_m, d)` is unimodular, and a shift by `d` is a shift by `w·c` followed by an
elementary operation adding a multiple of `a_last` — which does not change unimodularity. -/
theorem exists_stableRange_vector {R : Type*} [CommRing R] [IsDedekindDomain R] :
    ∀ n : ℕ, 2 ≤ n → ∀ (a : Fin n → R) (c : R),
      (∃ u : Fin n → R, ∃ w : R, (∑ i, u i * a i) + w * c = 1) →
      ∃ x p : Fin n → R, ∑ i, p i * (a i + x i * c) = 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro a c h
      obtain ⟨u, w, hu⟩ := h
      rw [Fin.sum_univ_two] at hu
      obtain ⟨x, y, p, q, hpq⟩ :=
        exists_stableRange_two (a := a 0) (b := a 1) (c := c) ⟨u 0, u 1, w, hu⟩
      refine ⟨![x, y], ![p, q], ?_⟩
      rw [Fin.sum_univ_two]
      simpa using hpq
  | succ n hn ih =>
      intro a c h
      obtain ⟨u, w, hu⟩ := h
      rw [Fin.sum_univ_castSucc] at hu
      set A : R := a (Fin.last n) with hA
      set d : R := u (Fin.last n) * A + w * c with hd
      have hshort : ∃ u' : Fin n → R, ∃ w' : R,
          (∑ i, u' i * (a i.castSucc)) + w' * d = 1 := by
        refine ⟨fun i => u i.castSucc, 1, ?_⟩
        rw [hd]
        linear_combination hu
      obtain ⟨x, p, hxp⟩ := ih (fun i => a i.castSucc) d hshort
      refine ⟨Fin.snoc (fun i => x i * w) 0, Fin.snoc p (∑ i, p i * x i * u (Fin.last n)), ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
      have hexp : ∀ i : Fin n,
          p i * (a i.castSucc + x i * w * c) = p i * (a i.castSucc + x i * d)
            - p i * x i * u (Fin.last n) * A := by
        intro i
        rw [hd]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib, hxp,
        ← Finset.sum_mul]
      ring

end GaloisForLFunctions.HTGeometry
