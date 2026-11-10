import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfTheSquareOfAQuadraticRing

/-!
# The square of a cyclotomic ring has its contacts on a progression

Let `p` be a prime and `K` the field of the `p`-th roots of unity, of degree `p − 1`. Its zeta
function is `ζ(s) Π_{χ ≠ 1} L(s, χ)` over the characters modulo `p`, all of them primitive. A
prime `ℓ ≠ p` of order `f` modulo `p` carries `(p − 1)/f` prime ideals of norm `ℓ^f`, and `p`
carries one of norm `p`. Counted by their norms the ideals sit on the comb of the integers.

* **The contacts** (`vonMangoldt_add_sum_twistWeight`): the contact orders of the ideals at the
  norm `n` add up to `(p − 1)Λ(n)` for `n ≡ 1 (mod p)`, to `Λ(n)` for `p ∣ n`, and to `0`
  otherwise: by the orthogonality of the characters the contacts of the ring are those of `ℤ`
  on the progression `1 mod p`, with the multiplicity `p − 1`.
* **The pairing** (`tendsto_cyclotomicForm_add_contact`): the jets and counterterms of `ζ` and of
  the `p − 2` twisted parts, with twice these contacts, tend on a packet to
  `2 d₁ d₂ − Z_K(f)`, the sum over the zeros of the zeta function of `K`. The masses enter with
  `log(p^{p−2} n^{p−1}/(2π)^{p−1})`: the discriminant `p^{p−2}` is a product of densities
  (`cyclotomicForm_eq`).
* **The index law** (`negIndex_sum_zeroGram_le`, `negIndex_cyclotomicDefect_packets_le`): for a
  finite family of tempered configurations the sum of Weil's forms has at most as many negative
  squares as the configurations have zeros to the right of the line, counted over the family.
  On the square of the cyclotomic ring the defect of the pairing obeys this bound with the
  zeros of `ζ` and of the `L(s, χ)`.
* **Short packets** (`tendsto_cyclotomicForm_le_degrees_of_short`): for `p ≥ 128π` the
  inequality of Castelnuovo and Severi holds on the packets shorter than `log 2`, with the
  margin `∫f²/5000`.

So a number ring of any degree `p − 1` pairs on the comb of the integers, with contacts that the
splitting law places on an arithmetic progression, and with no datum besides contacts, jets and
the densities of combs.
-/

open Finset Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Several configurations -/

section Family

variable {ι : Type*} [Fintype ι]

theorem hermQuad_sum {κ : Type*} (s : Finset κ) (A : κ → Matrix ι ι ℂ) (x : ι → ℂ) :
    hermQuad (∑ i ∈ s, A i) x = ∑ i ∈ s, hermQuad (A i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermQuad]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermQuad_add, ih]

/-- **The index law of a finite family of configurations.** The sum of Weil's forms of finitely
many tempered configurations has, on every finite family of tests, at most as many negative
squares as the configurations have zeros to the right of the critical line. -/
theorem negIndex_sum_zeroGram_le {κ : Type*} [Fintype κ] (Z : κ → ZeroConfig)
    (hZ : ∀ i, SquareRootThreshold.TemperedConfig (Z i)) (F : ι → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hFc : ∀ i, HasCompactSupport (F i)) :
    (hermNegIndex (∑ i, ArithmeticCastelnuovoSeveri.zeroGram (Z i) F) : ℕ∞) ≤
      ∑ i, (ArithmeticCastelnuovoSeveri.rightZeros (Z i)).encard := by
  classical
  by_cases hfin : ∀ i, (ArithmeticCastelnuovoSeveri.rightZeros (Z i)).Finite
  · haveI : ∀ i, Fintype (ArithmeticCastelnuovoSeveri.rightZeros (Z i)) := fun i =>
      (hfin i).fintype
    have hcard : ∀ i, (ArithmeticCastelnuovoSeveri.rightZeros (Z i)).encard =
        (Fintype.card (ArithmeticCastelnuovoSeveri.rightZeros (Z i)) : ℕ∞) := fun i => by
      rw [(hfin i).encard_eq_coe_toFinset_card, Set.Finite.card_toFinset]
    rw [Finset.sum_congr rfl fun i _ => hcard i, ← Nat.cast_sum, ← Fintype.card_sigma]
    refine ENat.coe_le_coe.mpr (ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
      (fun k : Σ i, ArithmeticCastelnuovoSeveri.rightZeros (Z i) =>
        ArithmeticCastelnuovoSeveri.evalFunctional F (gammaOf (k.2 : ℂ))) fun x hx => ?_)
    rw [hermQuad_sum]
    exact Finset.sum_nonneg fun i _ =>
      hermQuad_zeroGram_nonneg_of_vanish (Z i) (hZ i) F hF hFc x fun ρ hρ hre =>
        hx ⟨i, ⟨ρ, hρ, hre⟩⟩
  · push Not at hfin
    obtain ⟨i, hi⟩ := hfin
    have htop : (⊤ : ℕ∞) ≤ ∑ i, (ArithmeticCastelnuovoSeveri.rightZeros (Z i)).encard := by
      rw [← (Set.not_finite.mp hi).encard_eq]
      exact Finset.single_le_sum
        (f := fun i => (ArithmeticCastelnuovoSeveri.rightZeros (Z i)).encard)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    exact le_top.trans htop

end Family

/-! ### The characters modulo a prime -/

variable {p : ℕ} [Fact p.Prime]

theorem one_lt_of_fact_prime (p : ℕ) [Fact p.Prime] : 1 < p := (Fact.out : p.Prime).one_lt

/-- Modulo a prime every nontrivial character is primitive. -/
theorem isPrimitive_of_ne_one {χ : DirichletCharacter ℂ p} (h : χ ≠ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
    (DirichletCharacter.conductor_dvd_level χ) with h1 | h1
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) h
  · exact h1

/-- The contacts of the ideals of the cyclotomic ring of conductor `p`, counted by their norms:
`(p − 1)Λ(n)` on the progression `n ≡ 1 (mod p)`, `Λ(n)` on the multiples of `p`, zero
elsewhere. -/
def cyclotomicWeight (p n : ℕ) : ℝ :=
  if (n : ZMod p) = 1 then ((p : ℝ) - 1) * Λ n else if (n : ZMod p) = 0 then Λ n else 0

/-- **The contacts of a cyclotomic ring lie on a progression.** The contact order of `ℤ` and the
twisted contacts of the nontrivial characters modulo `p` add up to the contacts of the ideals. -/
theorem vonMangoldt_add_sum_twistWeight (n : ℕ) :
    Λ n + ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, twistWeight χ.1 n =
      cyclotomicWeight p n := by
  classical
  have hp : p.Prime := Fact.out
  -- the sum over all characters, by orthogonality
  have hall : ∑ χ : DirichletCharacter ℂ p, (χ (n : ZMod p)).re =
      if (n : ZMod p) = 1 then (p : ℝ) - 1 else 0 := by
    rw [← Complex.re_sum, DirichletCharacter.sum_characters_eq ℂ (n : ZMod p), Nat.totient_prime hp]
    split_ifs
    · rw [Complex.natCast_re, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    · exact Complex.zero_re
  -- split off the trivial character
  have hsplit : ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, (χ.1 (n : ZMod p)).re =
      (∑ χ : DirichletCharacter ℂ p, (χ (n : ZMod p)).re) -
        ((1 : DirichletCharacter ℂ p) (n : ZMod p)).re := by
    rw [← Finset.sum_subtype (Finset.univ.erase (1 : DirichletCharacter ℂ p))
        (fun χ => by simp) fun χ : DirichletCharacter ℂ p => (χ (n : ZMod p)).re,
      ← Finset.add_sum_erase Finset.univ (fun χ : DirichletCharacter ℂ p => (χ (n : ZMod p)).re)
        (Finset.mem_univ 1)]
    ring
  have hone : ((1 : DirichletCharacter ℂ p) (n : ZMod p)).re =
      if (n : ZMod p) = 0 then 0 else 1 := by
    split_ifs with h0
    · rw [MulChar.map_nonunit _ (by rw [h0]; exact not_isUnit_zero), Complex.zero_re]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr h0), Complex.one_re]
  have hsum : ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, twistWeight χ.1 n =
      Λ n * ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, (χ.1 (n : ZMod p)).re := by
    rw [Finset.mul_sum]
    rfl
  rw [hsum, hsplit, hall, hone, cyclotomicWeight]
  by_cases h1 : (n : ZMod p) = 1
  · have h0 : (n : ZMod p) ≠ 0 := by
      rw [h1]
      exact one_ne_zero
    rw [if_pos h1, if_pos h1, if_neg h0]
    ring
  · by_cases h0 : (n : ZMod p) = 0
    · rw [if_neg h1, if_neg h1, if_pos h0, if_pos h0]
      ring
    · rw [if_neg h1, if_neg h1, if_neg h0, if_neg h0]
      ring

variable {f : ℝ → ℝ}

theorem weightedContact_cyclotomicWeight (f : ℝ → ℝ) (L N : ℕ) :
    weightedContact (cyclotomicWeight p) f L N =
      degreeContact f L N +
        ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, weightedContact (twistWeight χ.1) f L N := by
  rw [← weightedContact_vonMangoldt]
  unfold weightedContact
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← vonMangoldt_add_sum_twistWeight (p := p) k, add_div, add_mul, Finset.sum_div,
    Finset.sum_mul]

/-! ### The pairing -/

/-- The jets and counterterms of the pairing of the cyclotomic ring of conductor `p`: those of the
integers and of the twisted parts of the nontrivial characters. -/
def cyclotomicForm (p : ℕ) [Fact p.Prime] (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  degreeForm f L N + ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, twistedForm χ.1 f L N

/-- The sum over the zeros of the zeta function of the cyclotomic field of conductor `p` of a
packet: the zeros of `ζ` and of the `L(s, χ)`, `χ ≠ 1`. -/
def cyclotomicZeroSum (p : ℕ) [Fact p.Prime] (f : ℝ → ℝ) : ℝ :=
  zeroSum f + ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
    twistedZeroSum (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2) f

/-- **The pairing of the square of a cyclotomic ring is twice the product of the degrees minus
the sum over the zeros of its zeta function.** -/
theorem tendsto_cyclotomicForm_add_contact (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => cyclotomicForm p f (3 * K) N +
        2 * weightedContact (cyclotomicWeight p) f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        cyclotomicZeroSum p f)) := by
  have h1 := tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp
  have h2 := tendsto_finsetSum
    (Finset.univ : Finset {χ : DirichletCharacter ℂ p // χ ≠ 1}) fun χ _ =>
      tendsto_twistedForm_add_twistedContact (one_lt_of_fact_prime p)
        (isPrimitive_of_ne_one χ.2) hf hfc hK hsupp
  have h := h1.add h2
  rw [show 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f +
        ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
          -twistedZeroSum (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2) f =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        cyclotomicZeroSum p f by
    rw [cyclotomicZeroSum, Finset.sum_neg_distrib]
    ring] at h
  refine h.congr fun N => ?_
  rw [cyclotomicForm, weightedContact_cyclotomicWeight, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- **The counterterm of a cyclotomic ring.** The jets of the integers enter `p − 1` times, and
the mass with `(p − 2) log p`, the logarithm of the discriminant `p^{p−2}`, besides `p − 1`
times the counterterm of the integers. -/
theorem cyclotomicForm_eq (f : ℝ → ℝ) (L N : ℕ) :
    cyclotomicForm p f L N = ((p : ℝ) - 1) * degreeForm f L N -
      ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1}, placeJet χ.1 f L N -
      ((p : ℝ) - 2) * Real.log p * ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n := by
  classical
  have hp : p.Prime := Fact.out
  have hcard : (Fintype.card {χ : DirichletCharacter ℂ p // χ ≠ 1} : ℝ) = (p : ℝ) - 2 := by
    have h1 : Fintype.card {χ : DirichletCharacter ℂ p // χ ≠ 1} =
        Fintype.card (DirichletCharacter ℂ p) - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have h2 : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
      rw [← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p, Nat.totient_prime hp]
    have h2p : 2 ≤ p := hp.two_le
    rw [h1, h2, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  unfold cyclotomicForm twistedForm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hcard]
  ring

/-! ### The Hodge index -/

section Index

variable {ι : Type*} [Fintype ι]

/-- The sum over the zeros of the zeta function of the cyclotomic field on a combination of
packets is the quadratic form of the Gram matrices of the zeros. -/
theorem cyclotomicZeroSum_packetCombination {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℝ) :
    cyclotomicZeroSum p (packetCombination f x) =
      hermQuad (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
          (fun i u => ((f i u : ℝ) : ℂ)) +
        ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
          ArithmeticCastelnuovoSeveri.zeroGram
            (_root_.RHTower.dirichletZeros (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2))
            fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)) := by
  rw [cyclotomicZeroSum, hermQuad_add, hermQuad_sum, zeroSum_packetCombination hf hfc x]
  congr 1
  exact Finset.sum_congr rfl fun χ _ =>
    twistedZeroSum_packetCombination (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2) hf hfc x

/-- **The index law on the square of a cyclotomic ring.** On every finite family of packets the
defect `2 d₁ d₂ − D·D` of the pairing has at most as many negative squares as `ζ` and the
`L(s, χ)`, `χ ≠ 1` modulo `p`, together have zeros to the right of the critical line. -/
theorem negIndex_cyclotomicDefect_packets_le {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
          (fun i u => ((f i u : ℝ) : ℂ)) +
        ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
          ArithmeticCastelnuovoSeveri.zeroGram
            (_root_.RHTower.dirichletZeros (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2))
            fun i u => ((f i u : ℝ) : ℂ)) : ℕ∞) ≤
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard +
        ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
          (ArithmeticCastelnuovoSeveri.rightZeros
            (_root_.RHTower.dirichletZeros (one_lt_of_fact_prime p)
              (isPrimitive_of_ne_one χ.2))).encard := by
  classical
  have hF : ∀ i, ContDiff ℝ 2 fun u => ((f i u : ℝ) : ℂ) := fun i =>
    contDiff_ofReal_packet (hf i)
  have hFc : ∀ i, HasCompactSupport fun u => ((f i u : ℝ) : ℂ) := fun i =>
    hasCompactSupport_ofReal_packet (hfc i)
  have h := negIndex_sum_zeroGram_le
    (fun o : Option {χ : DirichletCharacter ℂ p // χ ≠ 1} =>
      o.elim zetaZeroConfig fun χ =>
        _root_.RHTower.dirichletZeros (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2))
    (fun o => by
      cases o with
      | none => exact SquareRootThreshold.temperedConfig_zetaZeroConfig
      | some χ => exact temperedConfig_dirichletZeros (one_lt_of_fact_prime p)
          (isPrimitive_of_ne_one χ.2))
    (fun i u => ((f i u : ℝ) : ℂ)) hF hFc
  rw [Fintype.sum_option, Fintype.sum_option] at h
  rw [ArithmeticCastelnuovoSeveri.weilGram_eq_zeroGram _ hF hFc]
  exact h

end Index

/-! ### Short packets -/

/-- **The inequality on the square of a cyclotomic ring where no contact enters.** For a prime
`p ≥ 128π` and a packet shorter than `log 2` the pairing has a limit, at most twice the product
of the degrees minus `∫ f²/5000`. -/
theorem tendsto_cyclotomicForm_le_degrees_of_short (hlarge : 128 * π ≤ p)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {c a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * a < Real.log 2) (hshort : ∀ u, a < |u - c| → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => cyclotomicForm p f (3 * K) N +
          2 * weightedContact (cyclotomicWeight p) f (3 * K) N) atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        1 / 5000 * ∫ u, f u ^ 2 := by
  refine ⟨_, tendsto_cyclotomicForm_add_contact hf hfc hK hsupp, ?_⟩
  have h1 := zeroSum_ge_of_width hf hfc (c := c) fun u hu => hshort u (by
    have := Real.log_two_lt_d9
    linarith)
  have h2 : 0 ≤ ∑ χ : {χ : DirichletCharacter ℂ p // χ ≠ 1},
      twistedZeroSum (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2) f :=
    Finset.sum_nonneg fun χ _ =>
      twistedZeroSum_nonneg_of_short (one_lt_of_fact_prime p) (isPrimitive_of_ne_one χ.2)
        (χ.1.even_or_odd.elim (fun he => Or.inr ⟨he, hlarge⟩) fun ho =>
          Or.inl ⟨ho, by linarith [Real.pi_pos]⟩) hf hfc ha0 ha hshort
  rw [cyclotomicZeroSum]
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
