import GaloisForLFunctions.RHTower.DeningerDynSysTiltInjective

/-!
# The tilting comparison is surjective

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.13
(`t1110`), the surjectivity half of `lim_{()^p} A ≅ A♭`.

Given a compatible system of `p`-power roots modulo `p`, lift each term arbitrarily and raise the
`(n+k)`-th lift to the power `p^k`.  The resulting sequence is Cauchy for the `(p)`-adic filtration
because a congruence modulo `p` improves to one modulo `p^{k+1}` after raising to the `p^k`-th
power, so a `p`-adically complete ring supplies a limit; those limits form the required element of
`lim_{()^p} A`.
-/

namespace RHTower

open Perfection

variable {A : Type*} [CommRing A] {p : ℕ}

/-- Raising to the `p`-th power improves a congruence modulo `p^{m+1}` to one modulo `p^{m+2}`. -/
theorem deningerDvd_sub_pow_step {m : ℕ} {u v : A} (h : (p : A) ^ (m + 1) ∣ u - v) :
    (p : A) ^ (m + 2) ∣ u ^ p - v ^ p := by
  have hp : (p : A) ∣ u - v :=
    dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
  have hgeom : (p : A) ∣ ∑ i ∈ Finset.range p, u ^ i * v ^ (p - 1 - i) := by
    have hf : ∀ r : A, (p : A) ∣ r ↔ Ideal.Quotient.mk (Ideal.span {(p : A)}) r = 0 := fun r => by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rw [hf, map_sub, sub_eq_zero] at hp
    rw [hf, RingHom.map_geom_sum₂, hp, geom_sum₂_self, mul_eq_zero_of_left]
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : A)})),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hsplit : ((p : A) ^ (m + 2)) = (p : A) * (p : A) ^ (m + 1) := by ring
  rw [← geom_sum₂_mul, hsplit]
  exact mul_dvd_mul hgeom h

/-- Divisibility by a power of `p` as a congruence for the `(p)`-adic filtration. -/
theorem deningerSMod_of_dvd {k : ℕ} {u v : A} (h : (p : A) ^ k ∣ u - v) :
    u ≡ v [SMOD ((Ideal.span {(p : A)}) ^ k • ⊤ : Submodule A A)] := by
  rw [SModEq.sub_mem]
  have hmem : u - v ∈ (Ideal.span {(p : A)}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h
  simpa using hmem

/-- The converse reading of the previous lemma. -/
theorem deningerDvd_of_sMod {k : ℕ} {u v : A}
    (h : u ≡ v [SMOD ((Ideal.span {(p : A)}) ^ k • ⊤ : Submodule A A)]) :
    (p : A) ^ k ∣ u - v := by
  rw [SModEq.sub_mem] at h
  have hmem : u - v ∈ (Ideal.span {(p : A)}) ^ k := by simpa using h
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem

/-- **Deninger, Proposition 14.13 (`t1110`), surjectivity.**  For a `p`-adically complete ring the
tilting comparison `lim_{()^p} A → lim_{()^p} (A / p)` is surjective. -/
theorem deningerTiltComparison_surjective [IsAdicComplete (Ideal.span {(p : A)}) A] :
    Function.Surjective (deningerTiltComparison (A := A) (p := p)) := by
  classical
  intro yb
  choose a ha using fun n : ℕ => Ideal.Quotient.mk_surjective (yb.1 n)
  set g : ℕ → ℕ → A := fun n k => (a (n + k)) ^ p ^ k with hg
  have hdvd_iff : ∀ r : A, (p : A) ∣ r ↔
      Ideal.Quotient.mk (Ideal.span {(p : A)}) r = 0 := fun r => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hstep : ∀ n k : ℕ, (p : A) ^ (k + 1) ∣ g n (k + 1) - g n k := by
    intro n k
    have hcong : (p : A) ∣ (a (n + k + 1)) ^ p - a (n + k) := by
      rw [hdvd_iff, map_sub, map_pow, ha, ha, sub_eq_zero]
      exact yb.2 (n + k)
    have hd := dvd_sub_pow_of_dvd_sub hcong k
    rw [← pow_mul, ← pow_succ'] at hd
    have hidx : n + (k + 1) = n + k + 1 := by omega
    rw [hg]
    simpa [hidx] using hd
  have hcauchy : ∀ (n : ℕ) {i j : ℕ}, i ≤ j → (p : A) ^ i ∣ g n j - g n i := by
    intro n i j hij
    induction j with
    | zero =>
      have hi : i = 0 := Nat.le_zero.1 hij
      subst hi
      simp
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have hij' : i ≤ j := Nat.lt_succ_iff.1 h
        have h1 := ih hij'
        have h2 : (p : A) ^ i ∣ g n (j + 1) - g n j :=
          dvd_trans (pow_dvd_pow _ (by omega)) (hstep n j)
        have hsplit : g n (j + 1) - g n i = (g n (j + 1) - g n j) + (g n j - g n i) := by ring
        rw [hsplit]
        exact dvd_add h2 h1
      · have hi : i = j + 1 := le_antisymm hij h
        subst hi
        simp
  have hprec : ∀ n : ℕ, ∃ L : A, ∀ k : ℕ,
      g n k ≡ L [SMOD ((Ideal.span {(p : A)}) ^ k • ⊤ : Submodule A A)] := by
    intro n
    refine IsPrecomplete.prec inferInstance (f := g n) ?_
    intro i j hij
    refine deningerSMod_of_dvd ?_
    have h := hcauchy n hij
    have hneg : g n i - g n j = -(g n j - g n i) := by ring
    rw [hneg]
    exact Dvd.dvd.neg_right h
  choose L hL using hprec
  have hLdvd : ∀ n k : ℕ, (p : A) ^ k ∣ g n k - L n := fun n k => deningerDvd_of_sMod (hL n k)
  have hgpow : ∀ n k : ℕ, (g (n + 1) (k + 1)) ^ p = g n (k + 2) := by
    intro n k
    rw [hg]
    simp only
    rw [← pow_mul, ← pow_succ]
    congr 2
    omega
  have hpow : ∀ n : ℕ, (L (n + 1)) ^ p = L n := by
    intro n
    rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A)})]
    intro k
    refine deningerSMod_of_dvd ?_
    have hkey : (p : A) ^ (k + 2) ∣ (L (n + 1)) ^ p - L n := by
      have h1 : (p : A) ^ (k + 1) ∣ g (n + 1) (k + 1) - L (n + 1) := hLdvd (n + 1) (k + 1)
      have h2 : (p : A) ^ (k + 2) ∣ (g (n + 1) (k + 1)) ^ p - (L (n + 1)) ^ p :=
        deningerDvd_sub_pow_step h1
      rw [hgpow n k] at h2
      have h3 : (p : A) ^ (k + 2) ∣ g n (k + 2) - L n := hLdvd n (k + 2)
      have hsplit : (L (n + 1)) ^ p - L n
          = (g n (k + 2) - L n) - (g n (k + 2) - (L (n + 1)) ^ p) := by ring
      rw [hsplit]
      exact dvd_sub h3 h2
    exact dvd_trans (pow_dvd_pow _ (by omega)) hkey
  refine ⟨⟨L, fun n => hpow n⟩, ?_⟩
  refine Subtype.ext (funext fun n => ?_)
  show Ideal.Quotient.mk (Ideal.span {(p : A)}) (L n) = yb.1 n
  have h1 : (p : A) ^ 1 ∣ g n 1 - L n := hLdvd n 1
  have h2 : Ideal.Quotient.mk (Ideal.span {(p : A)}) (g n 1)
      = Ideal.Quotient.mk (Ideal.span {(p : A)}) (L n) := by
    rw [← sub_eq_zero, ← map_sub, ← hdvd_iff]
    simpa using h1
  rw [← h2, hg]
  simp only
  rw [pow_one, map_pow, ha]
  exact yb.2 n

/-- **Deninger, Proposition 14.13 (`t1110`).**  For a `p`-adically complete ring the tilting
comparison is a multiplicative bijection `lim_{()^p} A ≅ A♭`; this is the identification
underlying the correspondence between pointed multiplicative maps out of `lim_{()^p} A` and ring
homomorphisms out of the tilt. -/
noncomputable def deningerTiltEquiv [IsAdicComplete (Ideal.span {(p : A)}) A] :
    Perfection A p ≃* Perfection (A ⧸ Ideal.span {(p : A)}) p :=
  MulEquiv.ofBijective deningerTiltComparison
    ⟨deningerTiltComparison_injective, deningerTiltComparison_surjective⟩

@[simp] theorem deningerTiltEquiv_apply [IsAdicComplete (Ideal.span {(p : A)}) A]
    (x : Perfection A p) : deningerTiltEquiv x = deningerTiltComparison x := rfl

end RHTower
