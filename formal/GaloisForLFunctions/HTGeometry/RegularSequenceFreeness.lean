import GaloisForLFunctions.HTGeometry.DegreewiseRegularity

/-!
# A regular sequence of linear forms makes a graded ring free over the polynomial subring

Let `I ⊆ R = K[x]` be a homogeneous ideal, `l_1, …, l_d` linear forms forming a regular sequence on
`R/I`, and `e_i` homogeneous elements whose images form a `K`-basis of `R/(I + (l))`.  Then the
`e_i` form a basis of `R/I` over `K[l]`:

* `eq_zero_of_sum_aeval_mul_mem` — **independence**, with no grading: reduce a relation modulo
  `l_1` (the constant terms in `y_1` vanish by induction on `d`), divide by the regular element
  `l_1`, and descend on the degree in `y_1`;
* `spannedMod_all` — **generation**, the graded Nakayama argument: a homogeneous element of degree
  `n` is a `K`-combination of the `e_i` plus `Σ l_j g_j` modulo `I`, with `g_j` of degree `n − 1`.

Freeness gives the coprime regularity used for unmixedness
(`mem_sup_span_of_isRelPrime`): if `c, c' ∈ K[y]` are coprime, then `l(c')` is a nonzerodivisor
modulo `I + (l(c))`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

section Independence

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra K R]

/-- `l` is a regular sequence modulo `I`. -/
def IsRegSeqMod : {d : ℕ} → Ideal R → (Fin d → R) → Prop
  | 0, _, _ => True
  | _ + 1, I, l => (∀ x, l 0 * x ∈ I → x ∈ I) ∧ IsRegSeqMod (I ⊔ Ideal.span {l 0}) (Fin.tail l)

theorem sup_span_range_tail (I : Ideal R) {d : ℕ} (l : Fin (d + 1) → R) :
    I ⊔ Ideal.span {l 0} ⊔ Ideal.span (Set.range (Fin.tail l)) = I ⊔ Ideal.span (Set.range l) := by
  rw [sup_assoc, ← Ideal.span_union]
  congr 2
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range, Fin.tail]
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩
  · rintro ⟨i, rfl⟩
    refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i

theorem aeval_eq_eval₂_finSuccEquiv {d : ℕ} (l : Fin (d + 1) → R) (p : MvPolynomial (Fin (d + 1)) K) :
    aeval l p = Polynomial.eval₂ (aeval (Fin.tail l) : MvPolynomial (Fin d) K →ₐ[K] R).toRingHom
      (l 0) (finSuccEquiv K d p) := by
  have h : (aeval l : MvPolynomial (Fin (d + 1)) K →ₐ[K] R).toRingHom =
      (Polynomial.eval₂RingHom (aeval (Fin.tail l) : MvPolynomial (Fin d) K →ₐ[K] R).toRingHom
        (l 0)).comp
        (finSuccEquiv K d : MvPolynomial (Fin (d + 1)) K →+* _) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) fun i => ?_
    · simp only [RingHom.coe_coe, RingHom.comp_apply]
      rw [show (finSuccEquiv K d (C c)) = Polynomial.C (C c) from (finSuccEquiv K d).commutes c]
      simp
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ, Fin.tail]
  exact congrArg (fun φ : MvPolynomial (Fin (d + 1)) K →+* R => φ p) h

variable {ι : Type*} [Fintype ι]

theorem mk_sum_aeval_mul {d : ℕ} (J : Ideal R) (l : Fin d → R) (e : ι → R)
    (c : ι → K) :
    Ideal.Quotient.mk J (∑ i, aeval l (C (c i) : MvPolynomial (Fin d) K) * e i) =
      ∑ i, c i • Ideal.Quotient.mk J (e i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_C, map_mul, Algebra.smul_def, Ideal.Quotient.mk_algebraMap]

/-- **Independence.**  A relation `Σ l(b_i) e_i ∈ I` with coefficients in `K[y]` is trivial. -/
theorem eq_zero_of_sum_aeval_mul_mem : ∀ {d : ℕ} (I : Ideal R) (l : Fin d → R), IsRegSeqMod I l →
    ∀ (e : ι → R), LinearIndependent K (fun i => Ideal.Quotient.mk (I ⊔ Ideal.span (Set.range l)) (e i)) →
    ∀ b : ι → MvPolynomial (Fin d) K, (∑ i, aeval l (b i) * e i) ∈ I → b = 0 := by
  intro d
  induction d with
  | zero =>
      intro I l _ e he b hb
      have hb' : ∀ i, b i = C (coeff 0 (b i)) := fun i => eq_C_of_isEmpty (b i)
      have hsum : ∑ i, coeff 0 (b i) • Ideal.Quotient.mk (I ⊔ Ideal.span (Set.range l)) (e i) = 0 := by
        rw [← mk_sum_aeval_mul, Ideal.Quotient.eq_zero_iff_mem]
        refine Ideal.mem_sup_left ?_
        convert hb using 3 with i
        rw [← hb' i]
      have h0 := Fintype.linearIndependent_iff.mp he _ hsum
      funext i
      rw [hb' i, h0 i, map_zero, Pi.zero_apply]
  | succ d ih =>
      intro I l hreg e he
      have he' : LinearIndependent K (fun i => Ideal.Quotient.mk
          (I ⊔ Ideal.span {l 0} ⊔ Ideal.span (Set.range (Fin.tail l))) (e i)) := by
        rw [sup_span_range_tail]; exact he
      set E := finSuccEquiv K d
      -- the constant terms in `y_1` vanish
      have hconst : ∀ b : ι → MvPolynomial (Fin (d + 1)) K, (∑ i, aeval l (b i) * e i) ∈ I →
          ∀ i, (E (b i)).coeff 0 = 0 := by
        intro b hb
        have hsplit : ∀ i, aeval l (b i) =
            aeval (Fin.tail l) ((E (b i)).coeff 0) + l 0 * aeval l (E.symm (E (b i)).divX) := by
          intro i
          rw [aeval_eq_eval₂_finSuccEquiv, aeval_eq_eval₂_finSuccEquiv, AlgEquiv.apply_symm_apply]
          conv_lhs => rw [← Polynomial.X_mul_divX_add (E (b i))]
          rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
          ring
        have hmem : (∑ i, aeval (Fin.tail l) ((E (b i)).coeff 0) * e i) ∈ I ⊔ Ideal.span {l 0} := by
          have : (∑ i, aeval (Fin.tail l) ((E (b i)).coeff 0) * e i) =
              (∑ i, aeval l (b i) * e i) -
                l 0 * ∑ i, aeval l (E.symm (E (b i)).divX) * e i := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hsplit i]; ring
          rw [this]
          exact Ideal.sub_mem _ (Ideal.mem_sup_left hb)
            (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
        have := ih (I ⊔ Ideal.span {l 0}) (Fin.tail l) hreg.2 e he' _ hmem
        exact fun i => congrFun this i
      suffices H : ∀ n (b : ι → MvPolynomial (Fin (d + 1)) K), (∀ i, (E (b i)).natDegree ≤ n) →
          (∑ i, aeval l (b i) * e i) ∈ I → b = 0 by
        intro b hb
        exact H _ b (fun i => Finset.le_sup (f := fun i => (E (b i)).natDegree)
          (Finset.mem_univ i)) hb
      intro n
      induction n with
      | zero =>
          intro b hdeg hb
          have hc := hconst b hb
          funext i
          have hEi : E (b i) = 0 := by
            rw [Polynomial.eq_C_of_natDegree_le_zero (hdeg i), hc i, map_zero]
          rw [Pi.zero_apply, ← E.symm_apply_apply (b i), hEi, map_zero]
      | succ n ihn =>
          intro b hdeg hb
          have hc := hconst b hb
          set b' : ι → MvPolynomial (Fin (d + 1)) K := fun i => E.symm (E (b i)).divX with hb'
          have hEb : ∀ i, E (b i) = Polynomial.X * E (b' i) := by
            intro i
            rw [hb', AlgEquiv.apply_symm_apply]
            conv_lhs => rw [← Polynomial.X_mul_divX_add (E (b i))]
            rw [hc i, map_zero, add_zero]
          have hfac : ∀ i, aeval l (b i) = l 0 * aeval l (b' i) := by
            intro i
            rw [aeval_eq_eval₂_finSuccEquiv, aeval_eq_eval₂_finSuccEquiv (p := b' i), hEb i,
              Polynomial.eval₂_mul, Polynomial.eval₂_X]
          have hb'mem : (∑ i, aeval l (b' i) * e i) ∈ I := by
            refine hreg.1 _ ?_
            rw [Finset.mul_sum]
            convert hb using 2 with i
            rw [hfac i]; ring
          have hdeg' : ∀ i, (E (b' i)).natDegree ≤ n := by
            intro i
            rw [hb', AlgEquiv.apply_symm_apply, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
            have := hdeg i
            omega
          have h0 := ihn b' hdeg' hb'mem
          funext i
          rw [Pi.zero_apply, ← E.symm_apply_apply (b i), hEb i, show b' i = 0 from congrFun h0 i,
            map_zero, mul_zero, map_zero]

end Independence

section Spanning

variable {σ : Type*} {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- `p` is a `K[l]`-combination of the `e_i` modulo `I`. -/
def SpannedMod (I : Ideal (MvPolynomial σ K)) {d : ℕ} (l : Fin d → MvPolynomial σ K)
    (e : ι → MvPolynomial σ K) (p : MvPolynomial σ K) : Prop :=
  ∃ b : ι → MvPolynomial (Fin d) K, p - ∑ i, aeval l (b i) * e i ∈ I

variable {I : Ideal (MvPolynomial σ K)} {d : ℕ} {l : Fin d → MvPolynomial σ K}
  {e : ι → MvPolynomial σ K}

theorem SpannedMod.add {p q : MvPolynomial σ K} (hp : SpannedMod I l e p) (hq : SpannedMod I l e q) :
    SpannedMod I l e (p + q) := by
  obtain ⟨b, hb⟩ := hp
  obtain ⟨b', hb'⟩ := hq
  refine ⟨b + b', ?_⟩
  convert I.add_mem hb hb' using 1
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem spannedMod_of_mem {p : MvPolynomial σ K} (hp : p ∈ I) : SpannedMod I l e p :=
  ⟨0, by simpa using hp⟩

theorem SpannedMod.mul_C {p : MvPolynomial σ K} (hp : SpannedMod I l e p) (c : K) :
    SpannedMod I l e (C c * p) := by
  obtain ⟨b, hb⟩ := hp
  refine ⟨fun i => C c * b i, ?_⟩
  convert I.mul_mem_left (C c) hb using 1
  simp only [map_mul, aeval_C, mul_sub, Finset.mul_sum, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem SpannedMod.mul_l {p : MvPolynomial σ K} (hp : SpannedMod I l e p) (j : Fin d) :
    SpannedMod I l e (l j * p) := by
  obtain ⟨b, hb⟩ := hp
  refine ⟨fun i => X j * b i, ?_⟩
  convert I.mul_mem_left (l j) hb using 1
  simp only [map_mul, aeval_X, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem spannedMod_e (i : ι) : SpannedMod I l e (e i) := by
  classical
  refine ⟨fun k => if k = i then 1 else 0, ?_⟩
  have h : ∑ k, aeval l ((fun k => if k = i then (1 : MvPolynomial (Fin d) K) else 0) k) * e k =
      e i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h, sub_self]
  exact I.zero_mem

theorem spannedMod_sum {s : Finset β} {f : β → MvPolynomial σ K}
    (h : ∀ k ∈ s, SpannedMod I l e (f k)) : SpannedMod I l e (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact spannedMod_of_mem (by simp)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem homogeneousComponent_zero_mul_of_isHomogeneous_one {f : MvPolynomial σ K}
    (hf : f.IsHomogeneous 1) (g : MvPolynomial σ K) : homogeneousComponent 0 (f * g) = 0 := by
  have h0 : constantCoeff f = 0 := by
    rw [constantCoeff_eq]; exact hf.coeff_eq_zero (by simp)
  rw [homogeneousComponent_zero, ← constantCoeff_eq, map_mul, h0, zero_mul, map_zero]

/-- **Generation, degree by degree** (graded Nakayama). -/
theorem spannedMod_of_isHomogeneous (hI : IsHomogIdeal I) (hl : ∀ j, (l j).IsHomogeneous 1)
    (deg : ι → ℕ) (he : ∀ i, (e i).IsHomogeneous (deg i))
    (hspan : ∀ p, ∃ κ : ι → K, p - ∑ i, κ i • e i ∈ I ⊔ Ideal.span (Set.range l)) :
    ∀ n (p : MvPolynomial σ K), p.IsHomogeneous n → SpannedMod I l e p := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    obtain ⟨κ, hκ⟩ := hspan p
    obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.mp hκ
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht
    have hp' : p = ∑ i, κ i • e i + a + ∑ j, g j * l j := by
      rw [add_assoc, hat]; ring
    have hpn : p = homogeneousComponent n p :=
      (homogeneousComponent_of_mem hp).trans (if_pos rfl) |>.symm
    rw [hpn, hp', map_add, map_add, map_sum, map_sum]
    refine ((spannedMod_sum fun i _ => ?_).add (spannedMod_of_mem (hI n a ha))).add
      (spannedMod_sum fun j _ => ?_)
    · rw [map_smul, homogeneousComponent_of_mem (he i), smul_eq_C_mul]
      split_ifs
      · exact (spannedMod_e i).mul_C _
      · exact spannedMod_of_mem (by rw [mul_zero]; exact I.zero_mem)
    · rw [mul_comm]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [homogeneousComponent_zero_mul_of_isHomogeneous_one (hl j)]
        exact spannedMod_of_mem I.zero_mem
      · obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
        rw [homogeneousComponent_mul_left (hl j)]
        exact (ih m (by omega) _ (homogeneousComponent_isHomogeneous m _)).mul_l j

/-- **Generation.** -/
theorem spannedMod_all (hI : IsHomogIdeal I) (hl : ∀ j, (l j).IsHomogeneous 1)
    (deg : ι → ℕ) (he : ∀ i, (e i).IsHomogeneous (deg i))
    (hspan : ∀ p, ∃ κ : ι → K, p - ∑ i, κ i • e i ∈ I ⊔ Ideal.span (Set.range l))
    (p : MvPolynomial σ K) : SpannedMod I l e p := by
  rw [← sum_homogeneousComponent p]
  exact spannedMod_sum fun n _ =>
    spannedMod_of_isHomogeneous hI hl deg he hspan n _ (homogeneousComponent_isHomogeneous n p)

/-- **Coprime regularity.**  If `c, c' ∈ K[y]` are relatively prime, then `l(c')` is a
nonzerodivisor modulo `I + (l(c))`. -/
theorem mem_sup_span_of_isRelPrime (hI : IsHomogIdeal I) (hl : ∀ j, (l j).IsHomogeneous 1)
    (hreg : IsRegSeqMod I l) (deg : ι → ℕ) (he : ∀ i, (e i).IsHomogeneous (deg i))
    (hind : LinearIndependent K
      (fun i => Ideal.Quotient.mk (I ⊔ Ideal.span (Set.range l)) (e i)))
    (hspan : ∀ p, ∃ κ : ι → K, p - ∑ i, κ i • e i ∈ I ⊔ Ideal.span (Set.range l))
    {c c' : MvPolynomial (Fin d) K} (hcc : IsRelPrime c c') {x : MvPolynomial σ K}
    (hx : aeval l c' * x ∈ I ⊔ Ideal.span {aeval l c}) :
    x ∈ I ⊔ Ideal.span {aeval l c} := by
  obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  obtain ⟨bx, hbx⟩ := spannedMod_all hI hl deg he hspan x
  obtain ⟨by', hby⟩ := spannedMod_all hI hl deg he hspan y
  have e1 : (∑ i, aeval l (c' * bx i - c * by' i) * e i) =
      aeval l c' * (∑ i, aeval l (bx i) * e i) - aeval l c * (∑ i, aeval l (by' i) * e i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, map_mul, map_mul]
    ring
  have hrel : (∑ i, aeval l (c' * bx i - c * by' i) * e i) ∈ I := by
    have : (∑ i, aeval l (c' * bx i - c * by' i) * e i) =
        a - aeval l c' * (x - ∑ i, aeval l (bx i) * e i) +
          aeval l c * (y - ∑ i, aeval l (by' i) * e i) := by
      rw [e1]
      linear_combination (-1 : MvPolynomial σ K) * hat
    rw [this]
    exact I.add_mem (I.sub_mem ha (I.mul_mem_left _ hbx)) (I.mul_mem_left _ hby)
  have h0 := eq_zero_of_sum_aeval_mul_mem I l hreg e hind _ hrel
  have hdvd : ∀ i, c ∣ bx i := fun i => by
    have h1 : c' * bx i - c * by' i = 0 := congrFun h0 i
    exact hcc.dvd_of_dvd_mul_left ⟨by' i, sub_eq_zero.mp h1⟩
  choose z hz using hdvd
  have hS : (∑ i, aeval l (bx i) * e i) = aeval l c * ∑ i, aeval l (z i) * e i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz i, map_mul]
    ring
  have hx' : x = (x - ∑ i, aeval l (bx i) * e i) + aeval l c * ∑ i, aeval l (z i) * e i := by
    rw [← hS]; ring
  rw [hx']
  exact Ideal.add_mem _ (Ideal.mem_sup_left hbx)
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end Spanning

end

end GaloisForLFunctions.HTGeometry
