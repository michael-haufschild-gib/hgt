import GaloisForLFunctions.RHTower.Sieve.SmoothRough

/-!
# Euler bound for sums over smooth numbers

A sum of a nonnegative coprimality-multiplicative weight over the integers in `[1, Y]` whose prime
factors all lie in a finite set `P` is at most the corresponding finite Euler product

`∏_{p ∈ P} ∑_{i ≤ Y} g (p ^ i)`.

The proof is induction on `P`: splitting off one prime `p` writes each `P`-smooth `s ≤ Y`
uniquely as `p ^ v_p(s) · ord_compl[p] s`, with the second factor `P \ {p}`-smooth and coprime to
the first, and the resulting map into `range (Y+1) × (P \ {p})`-smooth numbers is injective.

Only the injection is used, so no exact factorisation count is needed and the inequality holds for
every `Y`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The integers in `[1, Y]` all of whose prime factors lie in `P`. -/
def smoothUpTo (P : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  {s ∈ Finset.Icc 1 Y | s.primeFactors ⊆ P}

theorem mem_smoothUpTo {P : Finset ℕ} {Y s : ℕ} :
    s ∈ smoothUpTo P Y ↔ (1 ≤ s ∧ s ≤ Y) ∧ s.primeFactors ⊆ P := by
  simp [smoothUpTo, Finset.mem_Icc]

theorem smoothUpTo_empty (Y : ℕ) : smoothUpTo ∅ Y ⊆ {1} := by
  intro s hs
  rw [mem_smoothUpTo] at hs
  have hzero : s.primeFactors = ∅ := Finset.subset_empty.1 hs.2
  have hs0 : s ≠ 0 := by omega
  have : s = 1 := by
    by_contra hcon
    have h1 : 1 < s := by omega
    obtain ⟨p, hp⟩ := (Nat.nonempty_primeFactors (n := s)).2 h1
    simp [hzero] at hp
  simp [this]

/-- **Euler bound for smooth sums.** -/
theorem sum_smoothUpTo_le {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg1 : g 1 = 1)
    (hgmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (Y : ℕ) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∑ s ∈ smoothUpTo P Y, g s ≤ ∏ p ∈ P, ∑ i ∈ Finset.range (Y + 1), g (p ^ i) := by
  classical
  intro P
  induction P using Finset.induction_on with
  | empty =>
      intro _
      rw [Finset.prod_empty]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (smoothUpTo_empty Y)
        (fun i _ _ => hg0 i)) ?_
      rw [Finset.sum_singleton, hg1]
  | insert p P' hpP' ih =>
      intro hprime
      have hp : p.Prime := hprime p (Finset.mem_insert_self p P')
      have hP' : ∀ q ∈ P', q.Prime := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      set B : Finset (ℕ × ℕ) := Finset.range (Y + 1) ×ˢ smoothUpTo P' Y with hB
      set F : ℕ × ℕ → ℝ := fun x => g (p ^ x.1) * g x.2 with hF
      set ι : ℕ → ℕ × ℕ := fun s => (s.factorization p, s / p ^ s.factorization p) with hι
      have hrecon : ∀ s ∈ smoothUpTo (insert p P') Y,
          p ^ (ι s).1 * (ι s).2 = s := by
        intro s hs
        rw [mem_smoothUpTo] at hs
        have hs0 : s ≠ 0 := by omega
        exact Nat.ordProj_mul_ordCompl_eq_self s p
      have hmemB : ∀ s ∈ smoothUpTo (insert p P') Y, ι s ∈ B := by
        intro s hs
        have hs' := hs
        rw [mem_smoothUpTo] at hs'
        obtain ⟨⟨hs1, hsY⟩, hsub⟩ := hs'
        have hs0 : s ≠ 0 := by omega
        have hdvd : p ^ s.factorization p ∣ s := Nat.ordProj_dvd s p
        have hle : p ^ s.factorization p ≤ s := Nat.le_of_dvd (by omega) hdvd
        have htwo : (2 : ℕ) ^ s.factorization p ≤ p ^ s.factorization p :=
          Nat.pow_le_pow_left hp.two_le _
        have hexp : s.factorization p ≤ Y := by
          have hlt : s.factorization p < 2 ^ s.factorization p := Nat.lt_two_pow_self
          omega
        have hcomp : s / p ^ s.factorization p ∈ smoothUpTo P' Y := by
          rw [mem_smoothUpTo]
          have hcpos : 0 < s / p ^ s.factorization p := Nat.ordCompl_pos p hs0
          refine ⟨⟨hcpos, ?_⟩, ?_⟩
          · exact le_trans (Nat.div_le_self _ _) hsY
          · intro q hq
            have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
            have hqdvd : q ∣ s / p ^ s.factorization p := Nat.dvd_of_mem_primeFactors hq
            have hq' : q ∈ s.primeFactors :=
              Nat.mem_primeFactors.2
                ⟨hqprime, dvd_trans hqdvd (Nat.ordCompl_dvd s p), hs0⟩
            have hqne : q ≠ p := by
              intro hcon
              exact Nat.not_dvd_ordCompl hp hs0 (hcon ▸ hqdvd)
            rcases Finset.mem_insert.1 (hsub hq') with h | h
            · exact absurd h hqne
            · exact h
        rw [hB, hι]
        exact Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hexp), hcomp⟩
      have hinj : ∀ x ∈ smoothUpTo (insert p P') Y, ∀ y ∈ smoothUpTo (insert p P') Y,
          ι x = ι y → x = y := by
        intro x hx y hy hxy
        have h1 := hrecon x hx
        have h2 := hrecon y hy
        rw [hxy] at h1
        exact h1.symm.trans h2
      have hval : ∀ s ∈ smoothUpTo (insert p P') Y, g s = F (ι s) := by
        intro s hs
        have hs' := hs
        rw [mem_smoothUpTo] at hs'
        have hs0 : s ≠ 0 := by omega
        have hs0' : s ≠ 0 := hs0
        have hcop : Nat.Coprime (p ^ s.factorization p) (s / p ^ s.factorization p) :=
          Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hs0')
        have := hgmul _ _ hcop
        rw [Nat.ordProj_mul_ordCompl_eq_self s p] at this
        rw [this, hF, hι]
      calc ∑ s ∈ smoothUpTo (insert p P') Y, g s
          = ∑ s ∈ smoothUpTo (insert p P') Y, F (ι s) := Finset.sum_congr rfl hval
        _ = ∑ x ∈ (smoothUpTo (insert p P') Y).image ι, F x := (Finset.sum_image hinj).symm
        _ ≤ ∑ x ∈ B, F x := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro x hx
              obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
              exact hmemB s hs
            · intro x _ _
              exact mul_nonneg (hg0 _) (hg0 _)
        _ = (∑ i ∈ Finset.range (Y + 1), g (p ^ i)) * ∑ s ∈ smoothUpTo P' Y, g s := by
            rw [hB, hF, Finset.sum_product, Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
        _ ≤ (∑ i ∈ Finset.range (Y + 1), g (p ^ i)) * ∏ q ∈ P', ∑ i ∈ Finset.range (Y + 1),
              g (q ^ i) := by
            refine mul_le_mul_of_nonneg_left (ih hP') ?_
            exact Finset.sum_nonneg fun i _ => hg0 _
        _ = ∏ q ∈ insert p P', ∑ i ∈ Finset.range (Y + 1), g (q ^ i) :=
            (Finset.prod_insert (f := fun q => ∑ i ∈ Finset.range (Y + 1), g (q ^ i)) hpP').symm

/-- The tilted reciprocal weight `t^{ω s} / s`. -/
noncomputable def smoothWeight (t : ℝ) (s : ℕ) : ℝ := t ^ s.primeFactors.card / (s : ℝ)

theorem smoothWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (s : ℕ) : 0 ≤ smoothWeight t s := by
  unfold smoothWeight
  positivity

theorem smoothWeight_one {t : ℝ} : smoothWeight t 1 = 1 := by
  simp [smoothWeight]

theorem smoothWeight_mul {t : ℝ} (a b : ℕ) (hab : Nat.Coprime a b) :
    smoothWeight t (a * b) = smoothWeight t a * smoothWeight t b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : b = 1 := by simpa [Nat.Coprime] using hab
    simp [hb, smoothWeight]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have ha1 : a = 1 := by simpa [Nat.Coprime] using hab
    simp [ha1, smoothWeight]
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hcard : (a * b).primeFactors.card = a.primeFactors.card + b.primeFactors.card := by
    rw [Nat.primeFactors_mul ha0 hb0]
    exact Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab)
  unfold smoothWeight
  rw [hcard, pow_add]
  push_cast
  field_simp

/-- The local factor of the smooth Euler bound. -/
theorem sum_smoothWeight_prime_pow_le {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    ∑ i ∈ Finset.range (Y + 1), smoothWeight t (p ^ i) ≤ 1 + t / ((p : ℝ) - 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  set r : ℝ := 1 / (p : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hppos]
    linarith
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hsplit : ∑ i ∈ Finset.range (Y + 1), smoothWeight t (p ^ i)
      = 1 + ∑ i ∈ Finset.range Y, t * r ^ (i + 1) := by
    rw [Finset.sum_range_succ']
    have hzero : smoothWeight t (p ^ 0) = 1 := by simp [smoothWeight]
    have hterm : ∀ i ∈ Finset.range Y, smoothWeight t (p ^ (i + 1)) = t * r ^ (i + 1) := by
      intro i _
      have hcard : (p ^ (i + 1)).primeFactors.card = 1 := by
        rw [Nat.primeFactors_pow p (Nat.succ_ne_zero i), Nat.Prime.primeFactors hp]
        simp
      unfold smoothWeight
      rw [hcard, hr]
      push_cast
      rw [pow_one, div_pow, one_pow]
      ring
    rw [Finset.sum_congr rfl hterm, hzero, add_comm]
  have hgeom : ∑ i ∈ Finset.range Y, t * r ^ (i + 1) = t * r * ∑ i ∈ Finset.range Y, r ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∑ i ∈ Finset.range Y, r ^ i ≤ 1 / (1 - r) := by
    have hne : r - 1 ≠ 0 := by intro h; linarith [h]
    have hne' : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
    have hpow : (0 : ℝ) ≤ r ^ Y := pow_nonneg hr0 Y
    have hkey : (r ^ Y - 1) / (r - 1) = (1 - r ^ Y) / (1 - r) := by
      field_simp
      ring
    rw [geom_sum_eq (by intro h; linarith [h] : r ≠ 1), hkey,
      div_le_div_iff_of_pos_right h1r]
    linarith
  have htr : 0 ≤ t * r := by positivity
  have hval : t * r * (1 / (1 - r)) = t / ((p : ℝ) - 1) := by
    rw [hr]
    field_simp
  have htail : ∑ i ∈ Finset.range Y, t * r ^ (i + 1) ≤ t / ((p : ℝ) - 1) := by
    rw [hgeom]
    calc t * r * ∑ i ∈ Finset.range Y, r ^ i ≤ t * r * (1 / (1 - r)) :=
          mul_le_mul_of_nonneg_left hbound htr
      _ = t / ((p : ℝ) - 1) := hval
  rw [hsplit]
  linarith

/-- **Smooth Euler bound.**  The tilted reciprocal sum over `z`-smooth integers up to `Y` is at
most the Euler product `∏_{p ≤ z} (1 + t/(p-1))`. -/
theorem sum_smoothWeight_le {t : ℝ} (ht : 0 ≤ t) (z Y : ℕ) :
    ∑ s ∈ smoothUpTo (Nat.primesLE z) Y, smoothWeight t s
      ≤ ∏ p ∈ Nat.primesLE z, (1 + t / ((p : ℝ) - 1)) := by
  refine le_trans (sum_smoothUpTo_le (smoothWeight_nonneg ht) smoothWeight_one
    (smoothWeight_mul) Y (Nat.primesLE z) (fun p hp => Nat.prime_of_mem_primesLE hp)) ?_
  refine Finset.prod_le_prod ?_ ?_
  · intro p _
    exact Finset.sum_nonneg fun i _ => smoothWeight_nonneg ht _
  · intro p hp
    exact sum_smoothWeight_prime_pow_le ht (Nat.prime_of_mem_primesLE hp) Y

end RHTower.Sieve
