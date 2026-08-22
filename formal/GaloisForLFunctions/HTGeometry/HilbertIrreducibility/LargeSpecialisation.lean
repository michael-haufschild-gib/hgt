import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Main
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Multivariate
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.SeveralVariables
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GaloisSpecialization

/-!
# Hilbert irreducibility with an unbounded set of good specialisations

The good rational specialisations produced by `Main` are `s₀ + 1/t` with `t` an arbitrarily large
integer, so they all lie in `(s₀, s₀+1)` for one integer `s₀`.  That `s₀` is only required to avoid
the finitely many roots of one nonzero polynomial, so it can be taken above any prescribed bound —
and then the good set is unbounded above.

This is the form the *open-set* applications need.  Composing with the birational substitution
`T = r + 1/Y`, whose good points then satisfy `Y > N`, places a good specialisation of the original
polynomial inside `(r, r + 1/N)`: an arbitrarily small interval around an arbitrarily chosen
rational centre.  No quantitative Hilbert irreducibility is needed for that.

## Main results

* `exists_int_not_root_gt` — a nonzero complex polynomial has a non-root integer above any bound.
* `exists_regular_int_gt`, `exists_regular_int_family_gt` — a regular integer above any bound.
* `infinite_gt_of_thin_bad` — the assembly, with the good set above `s₀`.
* `hilbert_irreducibility_gt`, `hilbert_irreducibility_family_gt` — **the good set is unbounded.**
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

/-- **A nonzero complex polynomial has a non-root integer above any prescribed bound.** -/
theorem exists_int_not_root_gt (N : ℤ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ m : ℤ, N < m ∧ p.eval ((m : ℤ) : ℂ) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hp (Polynomial.eq_zero_of_infinite_isRoot p ?_)
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (((N + 1 + (k : ℤ) : ℤ)) : ℂ)) ?_ ?_
  · intro a b h
    have h' : ((N + 1 + (a : ℤ) : ℤ) : ℂ) = ((N + 1 + (b : ℤ) : ℤ) : ℂ) := h
    have hz : (N + 1 + (a : ℤ)) = (N + 1 + (b : ℤ)) := by exact_mod_cast h'
    omega
  · intro k
    exact hcon (N + 1 + (k : ℤ)) (by omega)

/-- **A regular integer parameter above any prescribed bound.** -/
theorem exists_regular_int_gt (N : ℤ) {f : Polynomial (Polynomial ℤ)} {n : ℕ}
    (hn : f.natDegree = n) (hn1 : 1 ≤ n)
    (hsep : ((toQ f).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ)))).Separable) :
    ∃ s₀ : ℤ, N < s₀ ∧ Polynomial.aeval ((s₀ : ℤ) : ℂ) f.leadingCoeff ≠ 0 ∧
      ((toC f).map (Polynomial.evalRingHom ((s₀ : ℤ) : ℂ))).Separable := by
  obtain ⟨p, hpne, hp⟩ := exists_regular_poly hn hn1 hsep
  obtain ⟨s₀, hs₀N, hs₀⟩ := exists_int_not_root_gt N hpne
  obtain ⟨h1, h2⟩ := hp _ hs₀
  exact ⟨s₀, hs₀N, by rw [← leadingCoeff_toC]; exact h1, h2⟩

/-- **One regular integer parameter above any bound, for a whole finite family.** -/
theorem exists_regular_int_family_gt (N : ℤ) {ι : Type} [Fintype ι]
    (f : ι → Polynomial (Polynomial ℤ)) (n : ι → ℕ) (hn : ∀ i, (f i).natDegree = n i)
    (hn1 : ∀ i, 1 ≤ n i)
    (hsep : ∀ i, ((toQ (f i)).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ)))).Separable) :
    ∃ s₀ : ℤ, N < s₀ ∧ ∀ i, Polynomial.aeval ((s₀ : ℤ) : ℂ) (f i).leadingCoeff ≠ 0 ∧
      ((toC (f i)).map (Polynomial.evalRingHom ((s₀ : ℤ) : ℂ))).Separable := by
  classical
  choose p hpne hp using fun i => exists_regular_poly (hn i) (hn1 i) (hsep i)
  have hprodne : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hpne i
  obtain ⟨s₀, hs₀N, hs₀⟩ := exists_int_not_root_gt N hprodne
  refine ⟨s₀, hs₀N, fun i => ?_⟩
  have hi : (p i).eval ((s₀ : ℤ) : ℂ) ≠ 0 := by
    intro h
    apply hs₀
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  obtain ⟨h1, h2⟩ := hp i _ hi
  exact ⟨by rw [← leadingCoeff_toC]; exact h1, h2⟩

/-- **Assembly from gap-thin bad sets, with the good set above `s₀`.** -/
theorem infinite_gt_of_thin_bad {ι : Type} [Fintype ι]
    {s₀ : ℤ} {T : ℝ} {S : ι → Set ℤ} (hThin : ∀ j, Thin (S j)) {P : ℚ → Prop}
    (hgood : ∀ t : ℤ, max T 1 < (t : ℝ) → (∀ j, t ∉ S j) →
      P (((s₀ : ℤ) : ℚ) + ((t : ℤ) : ℚ)⁻¹)) :
    {b : ℚ | ((s₀ : ℤ) : ℚ) < b ∧ P b}.Infinite := by
  refine infinite_of_thin_bad (s₀ := s₀) (T := T) hThin
    (P := fun b => ((s₀ : ℤ) : ℚ) < b ∧ P b) ?_
  intro t ht hj
  refine ⟨?_, hgood t ht hj⟩
  have ht1 : (1 : ℝ) < (t : ℝ) := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : (0 : ℚ) < ((t : ℤ) : ℚ) := by
    have : (0 : ℝ) < (t : ℝ) := by linarith
    exact_mod_cast this
  have hinv : (0 : ℚ) < ((t : ℤ) : ℚ)⁻¹ := inv_pos.mpr htpos
  linarith

/-- **Hilbert's irreducibility theorem, integral form, with an unbounded good set.** -/
theorem hilbert_irreducibility_int_gt (N : ℤ) {f : Polynomial (Polynomial ℤ)} {n : ℕ}
    (hn : f.natDegree = n) (hn1 : 1 ≤ n)
    (hirr : Irreducible ((toQ f).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ))))) :
    {b : ℚ | ((N : ℤ) : ℚ) < b ∧
      Irreducible ((toQ f).map (Polynomial.evalRingHom b))}.Infinite := by
  classical
  obtain ⟨s₀, hs₀N, hlead0, hsepfib⟩ := exists_regular_int_gt N hn hn1 hirr.separable
  obtain ⟨T, S, hThin, hgood⟩ := exists_thin_bad hn hn1 hirr hlead0 hsepfib
  have hbase := infinite_gt_of_thin_bad (s₀ := s₀) (T := T) hThin
    (P := fun b => Irreducible ((toQ f).map (Polynomial.evalRingHom b)))
    (fun t htT htnot => hgood t (lt_of_le_of_lt (le_max_left _ _) htT) htnot)
  refine Set.Infinite.mono ?_ hbase
  rintro b ⟨hb1, hb2⟩
  refine ⟨?_, hb2⟩
  have hNs : ((N : ℤ) : ℚ) < ((s₀ : ℤ) : ℚ) := by exact_mod_cast hs₀N
  linarith

/-- **Hilbert's irreducibility theorem with an unbounded good set.** -/
theorem hilbert_irreducibility_gt (N : ℤ) {F : Polynomial (Polynomial ℚ)} (hirr : Irreducible F)
    (hdeg : 1 ≤ F.natDegree) :
    {b : ℚ | ((N : ℤ) : ℚ) < b ∧
      Irreducible (F.map (Polynomial.evalRingHom b))}.Infinite := by
  obtain ⟨f, hfdeg, hirrQK, htrans⟩ := exists_int_model hirr hdeg
  refine Set.Infinite.mono ?_
    (hilbert_irreducibility_int_gt N (n := f.natDegree) rfl hfdeg hirrQK)
  rintro b ⟨hb1, hb2⟩
  exact ⟨hb1, htrans b hb2⟩

/-- **Hilbert's irreducibility theorem for a finite family, integral form, with an unbounded good
set.** -/
theorem hilbert_irreducibility_int_family_gt (N : ℤ) {ι : Type} [Fintype ι]
    (f : ι → Polynomial (Polynomial ℤ)) (n : ι → ℕ)
    (hn : ∀ i, (f i).natDegree = n i) (hn1 : ∀ i, 1 ≤ n i)
    (hirr : ∀ i, Irreducible ((toQ (f i)).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ))))) :
    {b : ℚ | ((N : ℤ) : ℚ) < b ∧
      ∀ i, Irreducible ((toQ (f i)).map (Polynomial.evalRingHom b))}.Infinite := by
  classical
  obtain ⟨s₀, hs₀N, hreg⟩ := exists_regular_int_family_gt N f n hn hn1
    (fun i => (hirr i).separable)
  choose T S hThin hgood using fun i =>
    exists_thin_bad (hn i) (hn1 i) (hirr i) (hreg i).1 (hreg i).2
  set T' : ℝ := ∑ i, max (T i) 0 with hT'
  have hTle : ∀ i, T i ≤ T' := by
    intro i
    refine le_trans (le_max_left _ 0) ?_
    exact Finset.single_le_sum (f := fun k => max (T k) 0)
      (fun k _ => le_max_right _ _) (Finset.mem_univ i)
  have hbase := infinite_gt_of_thin_bad (s₀ := s₀) (T := T')
    (S := fun j : Σ i, {A : Finset (Fin (n i)) // A.Nonempty ∧ A ≠ Finset.univ} => S j.1 j.2)
    (fun j => hThin j.1 j.2)
    (P := fun b => ∀ i, Irreducible ((toQ (f i)).map (Polynomial.evalRingHom b))) ?_
  · refine Set.Infinite.mono ?_ hbase
    rintro b ⟨hb1, hb2⟩
    refine ⟨?_, hb2⟩
    have hNs : ((N : ℤ) : ℚ) < ((s₀ : ℤ) : ℚ) := by exact_mod_cast hs₀N
    linarith
  · intro t htT htnot i
    refine hgood i t (lt_of_le_of_lt (hTle i) (lt_of_le_of_lt (le_max_left _ 1) htT)) ?_
    intro j
    exact htnot ⟨i, j⟩

/-- **Hilbert's irreducibility theorem for a finite family, with an unbounded good set.** -/
theorem hilbert_irreducibility_family_gt (N : ℤ) {ι : Type} [Fintype ι]
    (F : ι → Polynomial (Polynomial ℚ)) (hirr : ∀ i, Irreducible (F i))
    (hdeg : ∀ i, 1 ≤ (F i).natDegree) :
    {b : ℚ | ((N : ℤ) : ℚ) < b ∧
      ∀ i, Irreducible ((F i).map (Polynomial.evalRingHom b))}.Infinite := by
  classical
  choose f hfdeg hirrQK htrans using fun i => exists_int_model (hirr i) (hdeg i)
  refine Set.Infinite.mono ?_
    (hilbert_irreducibility_int_family_gt N f (fun i => (f i).natDegree) (fun _ => rfl)
      hfdeg hirrQK)
  rintro b ⟨hb1, hb2⟩
  exact ⟨hb1, fun i => htrans i b (hb2 i)⟩

/-! ### One-variable specialisation of a multivariate polynomial, unbounded form -/

theorem exists_infinite_specialisation_gt (N : ℤ) {k : ℕ}
    {f : MvPolynomial (Fin k) (Polynomial ℚ)} (hf : Irreducible f) (hdeg : 0 < f.totalDegree) :
    {b : ℚ | ((N : ℤ) : ℚ) < b ∧
      Irreducible (MvPolynomial.map (Polynomial.evalRingHom b) f)}.Infinite := by
  classical
  obtain ⟨d, hd1, hfB⟩ : ∃ d : ℕ, 1 ≤ d ∧ KBounded d f := by
    refine ⟨(Finset.univ.sup fun j : Fin k => MvPolynomial.degreeOf j f) + 1, by omega, ?_⟩
    refine kBounded_of_degreeOf fun j => ?_
    have hle := Finset.le_sup (f := fun j : Fin k => MvPolynomial.degreeOf j f) (Finset.mem_univ j)
    omega
  have hd0 : 0 < d := hd1
  have hdk : 0 < d ^ k := pow_pos hd0 k
  have hfne : f ≠ 0 := hf.ne_zero
  have hPne : kron (Polynomial ℚ) d k f ≠ 0 := kron_ne_zero hd1 hfB hfne
  obtain ⟨n, g₀, g, hg₀, hgirr, hgdeg, hPeq⟩ := exists_factorisation hPne
  have hgne : ∀ i, g i ≠ 0 := fun i => (hgirr i).ne_zero
  have hnatP : (kron (Polynomial ℚ) d k f).natDegree < d ^ k := natDegree_kron_lt hdk hfB
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      subst hn
      have hPc : kron (Polynomial ℚ) d k f = Polynomial.C g₀ := by rw [hPeq]; simp
      have hfeq : f = MvPolynomial.C g₀ :=
        kron_injOn hd1 hfB (kBounded_C hd0 g₀) (by rw [hPc, kron_C])
      rw [hfeq, MvPolynomial.totalDegree_C] at hdeg
      omega
    · exact hn
  have hUV : ∀ t : Finset (Fin n), ∃ u v : MvPolynomial (Fin k) (Polynomial ℚ),
      KBounded d u ∧ KBounded d v ∧
        kron (Polynomial ℚ) d k u = ∏ i ∈ t, g i ∧
        kron (Polynomial ℚ) d k v = ∏ i ∈ tᶜ, g i := by
    intro t
    have hsplit : (∏ i ∈ t, g i) * ∏ i ∈ tᶜ, g i = ∏ i, g i := Finset.prod_mul_prod_compl t g
    have hdvdU : (∏ i ∈ t, g i) ∣ kron (Polynomial ℚ) d k f :=
      ⟨Polynomial.C g₀ * ∏ i ∈ tᶜ, g i, by rw [hPeq, ← hsplit]; ring⟩
    have hdvdV : (∏ i ∈ tᶜ, g i) ∣ kron (Polynomial ℚ) d k f :=
      ⟨Polynomial.C g₀ * ∏ i ∈ t, g i, by rw [hPeq, ← hsplit]; ring⟩
    obtain ⟨u, huB, hku⟩ := exists_kron_eq (k := k) hd1 (P := ∏ i ∈ t, g i) fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvdU hPne) (lt_of_lt_of_le hnatP hm))
    obtain ⟨v, hvB, hkv⟩ := exists_kron_eq (k := k) hd1 (P := ∏ i ∈ tᶜ, g i) fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvdV hPne) (lt_of_lt_of_le hnatP hm))
    exact ⟨u, v, huB, hvB, hku, hkv⟩
  choose ut vt hutB hvtB hkut hkvt using hUV
  have hexcl := fun t : Finset (Fin n) =>
    exists_exclusion d (MvPolynomial.C g₀ * ut t * vt t)
  choose e he0 he using hexcl
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin k →₀ ℕ, f.coeff a₀ ≠ 0 := by
    by_contra hc
    refine hfne (MvPolynomial.ext f 0 fun m => ?_)
    rw [MvPolynomial.coeff_zero]
    exact not_not.mp (fun h => hc ⟨m, h⟩)
  have hEne : ((∏ t : Finset (Fin n), e t) * g₀) * f.coeff a₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ => he0 t) hg₀) ha₀
  have hHIT := hilbert_irreducibility_family_gt N g hgirr hgdeg
  have hfin : {x : ℚ | (((∏ t : Finset (Fin n), e t) * g₀) * f.coeff a₀).IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot hEne
  refine Set.Infinite.mono ?_ (hHIT.sdiff hfin)
  rintro b ⟨⟨hbN, hbHIT⟩, hbE⟩
  refine ⟨hbN, ?_⟩
  have hEval : Polynomial.eval b (((∏ t : Finset (Fin n), e t) * g₀) * f.coeff a₀) ≠ 0 := hbE
  rw [Polynomial.eval_mul, Polynomial.eval_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hEval
  obtain ⟨⟨hEprod, hγ⟩, hcoeff0⟩ := hEval
  have het : ∀ t : Finset (Fin n), Polynomial.eval b (e t) ≠ 0 := by
    rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff] at hEprod
    exact fun t => hEprod t (Finset.mem_univ t)
  set q : Fin n → Polynomial ℚ :=
    fun i => Polynomial.map (Polynomial.evalRingHom b) (g i) with hq_def
  have hqirr : ∀ i, Irreducible (q i) := by
    intro i; simp only [hq_def]; exact hbHIT i
  have hqne : ∀ i, q i ≠ 0 := fun i => (hqirr i).ne_zero
  have hq1 : ∀ i, 1 ≤ (q i).natDegree := by
    intro i
    by_contra hc
    have h0 : (q i).natDegree = 0 := by omega
    obtain ⟨c, hc'⟩ := Polynomial.natDegree_eq_zero.mp h0
    refine (hqirr i).not_isUnit ?_
    rw [← hc']
    refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    intro hc0
    rw [hc0, map_zero] at hc'
    exact hqne i hc'.symm
  set fb : MvPolynomial (Fin k) ℚ := MvPolynomial.map (Polynomial.evalRingHom b) f with hfb_def
  have hfbB : KBounded d fb := by rw [hfb_def]; exact kBounded_map _ hfB
  have hkfb : kron ℚ d k fb = Polynomial.C (Polynomial.eval b g₀) * ∏ i, q i := by
    rw [hfb_def, ← kron_map, hPeq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    simp only [hq_def, Polynomial.coe_evalRingHom]
  have hfbne : fb ≠ 0 := by
    intro h0
    apply hcoeff0
    have hcz := congrArg (fun p => MvPolynomial.coeff a₀ p) h0
    simp only [hfb_def, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
      Polynomial.coe_evalRingHom] at hcz
    exact hcz
  have hnu : ¬ IsUnit fb := by
    intro hcu
    have h1 : IsUnit (kron ℚ d k fb) := hcu.map (kron ℚ d k)
    rw [hkfb] at h1
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit h1
    rw [Polynomial.natDegree_C_mul hγ, Polynomial.natDegree_prod _ _ (fun i _ => hqne i)] at h2
    obtain ⟨i0⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn1
    have h3 : 1 ≤ ∑ i, (q i).natDegree :=
      le_trans (hq1 i0) (Finset.single_le_sum (f := fun i => (q i).natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i0))
    omega
  refine ⟨hnu, fun u v huv => ?_⟩
  by_contra hcon
  have hu : ¬ IsUnit u := fun h => hcon (Or.inl h)
  have hv : ¬ IsUnit v := fun h => hcon (Or.inr h)
  have hune : u ≠ 0 := by rintro rfl; rw [zero_mul] at huv; exact hfbne huv
  have hvne : v ≠ 0 := by rintro rfl; rw [mul_zero] at huv; exact hfbne huv
  have huvB : KBounded d (u * v) := huv ▸ hfbB
  have huB : KBounded d u := kBounded_of_mul_left hd0 hune hvne huvB
  have hvB : KBounded d v := kBounded_of_mul_right hd0 hune hvne huvB
  have hmul : kron ℚ d k u * kron ℚ d k v = Polynomial.C (Polynomial.eval b g₀) * ∏ i, q i := by
    rw [← map_mul, ← huv, hkfb]
  have hCinv : Polynomial.C (Polynomial.eval b g₀)⁻¹ * Polynomial.C (Polynomial.eval b g₀)
      = (1 : Polynomial ℚ) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hγ, Polynomial.C_1]
  have hprod : (kron ℚ d k u * Polynomial.C (Polynomial.eval b g₀)⁻¹) * kron ℚ d k v
      = ∏ i, q i := by
    calc (kron ℚ d k u * Polynomial.C (Polynomial.eval b g₀)⁻¹) * kron ℚ d k v
        = Polynomial.C (Polynomial.eval b g₀)⁻¹ * (kron ℚ d k u * kron ℚ d k v) := by ring
      _ = Polynomial.C (Polynomial.eval b g₀)⁻¹ *
            (Polynomial.C (Polynomial.eval b g₀) * ∏ i, q i) := by rw [hmul]
      _ = (Polynomial.C (Polynomial.eval b g₀)⁻¹ * Polynomial.C (Polynomial.eval b g₀)) *
            ∏ i, q i := by ring
      _ = ∏ i, q i := by rw [hCinv, one_mul]
  have hqprime : ∀ i ∈ (Finset.univ : Finset (Fin n)), Prime (q i) := fun i _ =>
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (hqirr i)
  obtain ⟨t, -, hassoc0⟩ :=
    PrimeSubsetFactor.exists_subset_associated Finset.univ q hqprime _ _ hprod
  have hCunit : IsUnit (Polynomial.C (Polynomial.eval b g₀)⁻¹ : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hγ))
  have hassocU : Associated (kron ℚ d k u) (∏ i ∈ t, q i) :=
    Associated.trans ⟨hCunit.unit, by rw [hCunit.unit_spec]⟩ hassoc0
  have hassocV : Associated (kron ℚ d k v) (∏ i ∈ tᶜ, q i) := by
    rw [Finset.compl_eq_univ_sdiff]
    exact PrimeSubsetFactor.associated_sdiff_of_associated (Finset.subset_univ t) hqprime
      hprod hassoc0
  have hmapU : kron ℚ d k (MvPolynomial.map (Polynomial.evalRingHom b) (ut t))
      = ∏ i ∈ t, q i := by
    rw [← kron_map, hkut, Polynomial.map_prod]
  have hmapV : kron ℚ d k (MvPolynomial.map (Polynomial.evalRingHom b) (vt t))
      = ∏ i ∈ tᶜ, q i := by
    rw [← kron_map, hkvt, Polynomial.map_prod]
  obtain ⟨cu, hcu⟩ := hassocU
  obtain ⟨ru, hru, hruC⟩ := Polynomial.isUnit_iff.mp cu.isUnit
  obtain ⟨cv, hcv⟩ := hassocV
  obtain ⟨rv, hrv, hrvC⟩ := Polynomial.isUnit_iff.mp cv.isUnit
  have hIdU : u * MvPolynomial.C ru = MvPolynomial.map (Polynomial.evalRingHom b) (ut t) := by
    refine kron_injOn hd1 (kBounded_mul_C ru huB) (kBounded_map _ (hutB t)) ?_
    rw [map_mul, kron_C, hmapU, hruC]
    exact hcu
  have hIdV : v * MvPolynomial.C rv = MvPolynomial.map (Polynomial.evalRingHom b) (vt t) := by
    refine kron_injOn hd1 (kBounded_mul_C rv hvB) (kBounded_map _ (hvtB t)) ?_
    rw [map_mul, kron_C, hmapV, hrvC]
    exact hcv
  have hnuU : ¬ IsUnit (ut t) := by
    intro hU
    have h1 : IsUnit (u * MvPolynomial.C ru) := by
      rw [hIdU]
      exact hU.map (MvPolynomial.map (Polynomial.evalRingHom b))
    exact hu (isUnit_of_mul_isUnit_left h1)
  have hnuV : ¬ IsUnit (vt t) := by
    intro hV
    have h1 : IsUnit (v * MvPolynomial.C rv) := by
      rw [hIdV]
      exact hV.map (MvPolynomial.map (Polynomial.evalRingHom b))
    exact hv (isUnit_of_mul_isUnit_left h1)
  have hkw : kron (Polynomial ℚ) d k (MvPolynomial.C g₀ * ut t * vt t)
      = kron (Polynomial ℚ) d k f := by
    rw [map_mul, map_mul, kron_C, hkut, hkvt, hPeq, ← Finset.prod_mul_prod_compl t g, mul_assoc]
  by_cases hwB : KBounded d (MvPolynomial.C g₀ * ut t * vt t)
  · have hfeq : MvPolynomial.C g₀ * ut t * vt t = f := kron_injOn hd1 hwB hfB hkw
    rcases hf.isUnit_or_isUnit hfeq.symm with h | h
    · exact hnuU (isUnit_of_mul_isUnit_right h)
    · exact hnuV h
  · apply hwB
    refine he t b (het t) ?_
    have hmapw : MvPolynomial.map (Polynomial.evalRingHom b) (MvPolynomial.C g₀ * ut t * vt t)
        = (u * v) * MvPolynomial.C (Polynomial.eval b g₀ * ru * rv) := by
      rw [map_mul, map_mul, MvPolynomial.map_C, ← hIdU, ← hIdV, map_mul, map_mul]
      simp only [Polynomial.coe_evalRingHom]
      ring
    rw [hmapw, ← huv]
    exact kBounded_mul_C _ hfbB

/-! ### Several parameters, unbounded form -/

theorem hilbert_several_gt (N : ℤ) : ∀ (m : ℕ) (G : Polynomial (MvPolynomial (Fin m) ℚ))
    (g : MvPolynomial (Fin m) ℚ), Irreducible G → 1 ≤ G.natDegree → g ≠ 0 →
      ∃ y : Fin m → ℚ, (∀ i, ((N : ℤ) : ℚ) < y i) ∧ MvPolynomial.eval y g ≠ 0 ∧
        Irreducible (G.map (MvPolynomial.eval y)) ∧
        (G.map (MvPolynomial.eval y)).natDegree = G.natDegree := by
  intro m
  induction m with
  | zero =>
      intro G g hG hdeg hg
      have heq : (MvPolynomial.eval (Fin.elim0 : Fin 0 → ℚ))
          = (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => i.elim0)
        simp only [MvPolynomial.eval_C, MvPolynomial.isEmptyAlgEquiv,
          RingEquiv.toRingHom_eq_coe]
        exact (MvPolynomial.coeff_zero_C r).symm
      refine ⟨Fin.elim0, fun i => i.elim0, ?_, ?_, ?_⟩
      · rw [heq]
        exact fun h => hg ((MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.injective
          (by simpa using h))
      · rw [heq]
        have hmap : Polynomial.map
            ((MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.toRingHom) G
              = Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv G := rfl
        rw [hmap]
        exact (MulEquiv.irreducible_iff
          (Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv)).mpr hG
      · rw [heq]
        exact Polynomial.natDegree_map_eq_of_injective
          (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.injective G
  | succ m ih =>
      intro G g hG hdeg hg
      have hGne : G ≠ 0 := hG.ne_zero
      obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (Fin (m + 1)) (Polynomial ℚ),
          f = kill1 m ((MvPolynomial.finSuccEquiv ℚ (m + 1)).symm G) := ⟨_, rfl⟩
      have hfirr : Irreducible f := by
        rw [hf]
        exact (MulEquiv.irreducible_iff (kill1 m)).mpr
          ((MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℚ (m + 1)).symm).mpr hG)
      have hftd : 0 < f.totalDegree := by
        rcases Nat.eq_zero_or_pos f.totalDegree with h0 | h
        · exfalso
          obtain ⟨q, hq⟩ : ∃ q : Polynomial ℚ, f = MvPolynomial.C q :=
            ⟨MvPolynomial.coeff 0 f, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0⟩
          have h1 : (kill1 m).symm (MvPolynomial.C Polynomial.X)
              = MvPolynomial.X (1 : Fin (m + 2)) := by
            rw [← kill1_X_one m, AlgEquiv.symm_apply_apply]
          have h2 : (MvPolynomial.finSuccEquiv ℚ (m + 1)) (MvPolynomial.X (1 : Fin (m + 2)))
              = Polynomial.C (MvPolynomial.X (0 : Fin (m + 1))) := by
            rw [one_eq_succ_zero, MvPolynomial.finSuccEquiv_X_succ]
          have hXi : ∀ r : Polynomial ℚ,
              (MvPolynomial.finSuccEquiv ℚ (m + 1)) ((kill1 m).symm (MvPolynomial.C r))
                = Polynomial.C (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) r) := by
            intro r
            have key : ((MvPolynomial.finSuccEquiv ℚ (m + 1)).toAlgHom.comp
                  ((kill1 m).symm.toAlgHom.comp (IsScalarTower.toAlgHom ℚ (Polynomial ℚ)
                    (MvPolynomial (Fin (m + 1)) (Polynomial ℚ)))))
                = Polynomial.CAlgHom.comp
                    (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) := by
              refine Polynomial.algHom_ext ?_
              simp [MvPolynomial.algebraMap_eq, h1, h2]
            have hr := congrArg (fun F => F r) key
            simpa [MvPolynomial.algebraMap_eq] using hr
          have hGval : G = Polynomial.C
              (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) q) := by
            have hsymm : (kill1 m).symm f = (MvPolynomial.finSuccEquiv ℚ (m + 1)).symm G := by
              rw [hf, AlgEquiv.symm_apply_apply]
            rw [← hXi q, ← hq, hsymm, AlgEquiv.apply_symm_apply]
          rw [hGval, Polynomial.natDegree_C] at hdeg
          omega
        · exact h
      have hinf := exists_infinite_specialisation_gt N hfirr hftd
      have hfin1 : {c : ℚ | spec0 c g = 0}.Finite := finite_spec0_zero hg
      have hfin2 : {c : ℚ | spec0 c G.leadingCoeff = 0}.Finite :=
        finite_spec0_zero (Polynomial.leadingCoeff_ne_zero.mpr hGne)
      obtain ⟨c, ⟨⟨⟨hcN, hc⟩, hc1⟩, hc2⟩⟩ := ((hinf.sdiff hfin1).sdiff hfin2).nonempty
      have hc1' : spec0 c g ≠ 0 := hc1
      have hc2' : spec0 c G.leadingCoeff ≠ 0 := hc2
      have hdeg' : (G.map (spec0 c).toRingHom).natDegree = G.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hc2'
      have hGirr' : Irreducible (G.map (spec0 c).toRingHom) := by
        have h1 : Irreducible
            ((MvPolynomial.finSuccEquiv ℚ m).symm (G.map (spec0 c).toRingHom)) := by
          rw [← step_emb c G, ← hf]
          exact hc
        exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℚ m).symm).mp h1
      obtain ⟨y', hy'N, hy'g, hy'irr, hy'deg⟩ :=
        ih (G.map (spec0 c).toRingHom) (spec0 c g) hGirr' (by omega) hc1'
      have heval : (MvPolynomial.eval (Fin.cons c y') : MvPolynomial (Fin (m + 1)) ℚ →+* ℚ)
          = (MvPolynomial.eval y').comp (spec0 c).toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
        · simp
        · refine Fin.cases ?_ ?_ i
          · simp
          · intro j
            simp
      refine ⟨Fin.cons c y', ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hcN
        · intro j
          simpa using hy'N j
      · rw [show MvPolynomial.eval (Fin.cons c y') g
            = (MvPolynomial.eval y').comp (spec0 c).toRingHom g from by rw [heval]]
        exact hy'g
      · rw [heval, ← Polynomial.map_map]
        exact hy'irr
      · rw [heval, ← Polynomial.map_map, hy'deg, hdeg']

/-- **Hilbert irreducibility in several parameters, unbounded form.** -/
theorem hilbert_multivariate_gt (N : ℤ) {m : ℕ} {G : Polynomial (MvPolynomial (Fin m) ℚ)}
    (hG : Irreducible G) (hdeg : 1 ≤ G.natDegree) {g : MvPolynomial (Fin m) ℚ} (hg : g ≠ 0) :
    ∃ y : Fin m → ℚ, (∀ i, ((N : ℤ) : ℚ) < y i) ∧ MvPolynomial.eval y g ≠ 0 ∧
      Irreducible (G.map (MvPolynomial.eval y)) ∧
      (G.map (MvPolynomial.eval y)).natDegree = G.natDegree :=
  hilbert_several_gt N m G g hG hdeg hg

/-! ### Galois-preserving specialisation, unbounded form -/

theorem gal_card_of_specialisation_gt (N : ℤ) {m D : ℕ}
    {f : Polynomial (MvPolynomial (Fin m) ℚ)} (hf : f.Monic) (hfdeg : f.natDegree = D)
    (hsep : (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
        (FractionRing (MvPolynomial (Fin m) ℚ)))).Separable)
    (hgal : Nat.card (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
        (FractionRing (MvPolynomial (Fin m) ℚ)))).Gal = D.factorial)
    {g : MvPolynomial (Fin m) ℚ} (hg : g ≠ 0) :
    ∃ y : Fin m → ℚ, (∀ i, ((N : ℤ) : ℚ) < y i) ∧ MvPolynomial.eval y g ≠ 0 ∧
      Nat.card (f.map (MvPolynomial.eval y)).Gal = D.factorial := by
  classical
  have hFm : (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
      (FractionRing (MvPolynomial (Fin m) ℚ)))).Monic := hf.map _
  have hFdeg : (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
      (FractionRing (MvPolynomial (Fin m) ℚ)))).natDegree = D := by
    rw [hf.natDegree_map, hfdeg]
  obtain ⟨k, hk⟩ := exists_irreducible_resolvent
    ((algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))).comp
      (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ)) hFm hsep hFdeg hgal
  have hR0map : (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f).map
      (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ)))
      = resolvent k ((algebraMap (MvPolynomial (Fin m) ℚ)
          (FractionRing (MvPolynomial (Fin m) ℚ))).comp
        (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ))
        (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
          (FractionRing (MvPolynomial (Fin m) ℚ)))) :=
    resolvent_map k _ _ f
  have hR0irr : Irreducible (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f) :=
    Polynomial.Monic.irreducible_of_irreducible_map _ _
      (monic_resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f)
      (by rw [hR0map]; exact hk)
  have hR0deg : (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f).natDegree
      = D.factorial := by
    rw [natDegree_resolvent, Fintype.card_perm, Fintype.card_fin]
  obtain ⟨y, hyN, hy1, hy2, -⟩ := hilbert_multivariate_gt N hR0irr
    (by rw [hR0deg]; exact Nat.factorial_pos D) hg
  refine ⟨y, hyN, hy1, ?_⟩
  have hcomp : (MvPolynomial.eval y).comp (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ)
      = RingHom.id ℚ := by
    refine RingHom.ext fun q => ?_
    simp
  have hspec : (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f).map
      (MvPolynomial.eval y) = resolvent k (RingHom.id ℚ) (f.map (MvPolynomial.eval y)) := by
    rw [resolvent_map k _ (MvPolynomial.eval y) f, hcomp]
  rw [hspec] at hy2
  exact gal_card_of_irreducible_resolvent (RingHom.id ℚ) (hf.map _)
    (by rw [hf.natDegree_map, hfdeg]) hy2

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
