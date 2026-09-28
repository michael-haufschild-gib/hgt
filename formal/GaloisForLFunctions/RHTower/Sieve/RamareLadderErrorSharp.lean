import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplit
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RamareCofactorBlock
import GaloisForLFunctions.RHTower.Sieve.ElementaryHarmonicBounds

/-!
# The Ramaré ladder error without the multiplicity loss

The ladder error compares, for every designated prime `p` of the `j`-th block
`(S_j, S_j(1+η)]`, `S_j = Q(1+η)^j`, the cofactor polynomial over `m ≤ M/p`, `p ∤ m`, with the
common one over `m ≤ M/S_j`.  The difference consists of

* the boundary cofactors `M/p < m ≤ M/S_j`, whose products `n = pm` lie in `(M, M(1+η)]`;
* the cofactors divisible by `p`, whose products are divisible by `p²`.

Written as a Dirichlet polynomial in `n = pm`, the Ramaré weight `1/(ω_P(m)+1) ≤ 1/ω_P(n)` caps
every boundary coefficient by `1`, because at most `ω_P(n)` designated primes divide `n`.  Hence
the boundary part has energy at most `ηM + 1`, the `p²`-part at most `6M/Q`, and

`∫_{|w| ≤ W} ‖ladder error‖² ≤ 2(5π/2·W + 5e/2·⌊M(1+η)⌋)(ηM + 1 + 6M/Q)`,

with no factor `log M/log Q`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### Fibred phase sums -/

/-- A phase sum over an index set is the Dirichlet polynomial over the image, with the fibre sums as
coefficients. -/
theorem sum_mul_unitLogPhase_eq_logPoly {ι : Type*} [DecidableEq ι] (I : Finset ι) (ν : ι → ℕ)
    (b : ι → ℂ) (w : ℝ) :
    ∑ i ∈ I, b i * unitLogPhase w (ν i)
      = logPoly (fun n => ∑ i ∈ I with ν i = n, b i) (I.image ν) w := by
  rw [logPoly, ← Finset.sum_fiberwise_of_maps_to (g := ν) (t := I.image ν)
    (fun i hi => Finset.mem_image_of_mem ν hi)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2, unitLogPhase]

/-- **The fibred mean value theorem.**  The mean square of a phase sum is at most the mean value
factor times the energy of its fibre sums. -/
theorem integral_normSq_sum_unitLogPhase_le {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (ν : ι → ℕ) (b : ι → ℂ) (hν : ∀ i ∈ I, 0 < ν i) {N : ℕ} (hνN : ∀ i ∈ I, ν i ≤ N) {W : ℝ}
    (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, b i * unitLogPhase w (ν i)‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ))
          * ∑ n ∈ I.image ν, ‖∑ i ∈ I with ν i = n, b i‖ ^ (2 : ℕ) := by
  have h0 : (0 : ℕ) ∉ I.image ν := by
    intro h
    obtain ⟨i, hi, hi0⟩ := Finset.mem_image.mp h
    exact (hν i hi).ne' hi0
  have hN : ∀ n ∈ I.image ν, n ≤ N := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact hνN i hi
  simp_rw [sum_mul_unitLogPhase_eq_logPoly I ν b]
  exact integral_Icc_normSq_logPoly_le_energy _ h0 hN hW

/-- A fibre sum dominated by one unit per fibre has energy at most the size of the image. -/
theorem sum_normSq_fibre_le_card {ι : Type*} [DecidableEq ι] (I : Finset ι) (ν : ι → ℕ)
    (b : ι → ℂ) (hfib : ∀ n, ∑ i ∈ I with ν i = n, ‖b i‖ ≤ 1) :
    ∑ n ∈ I.image ν, ‖∑ i ∈ I with ν i = n, b i‖ ^ (2 : ℕ) ≤ ((I.image ν).card : ℝ) := by
  have hterm : ∀ n ∈ I.image ν, ‖∑ i ∈ I with ν i = n, b i‖ ^ (2 : ℕ) ≤ 1 := by
    intro n _
    have h1 : ‖∑ i ∈ I with ν i = n, b i‖ ≤ 1 := (norm_sum_le _ _).trans (hfib n)
    have h0 := norm_nonneg (∑ i ∈ I with ν i = n, b i)
    nlinarith
  calc ∑ n ∈ I.image ν, ‖∑ i ∈ I with ν i = n, b i‖ ^ (2 : ℕ)
      ≤ ∑ _n ∈ I.image ν, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((I.image ν).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ### The Ramaré weight caps the boundary coefficients -/

/-- `ω_P(pm) ≤ ω_P(m) + 1` for a prime `p` and a set `P` of primes. -/
theorem card_primeFactorsIn_mul_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {p : ℕ}
    (hp : p.Prime) (m : ℕ) :
    (primeFactorsIn P (p * m)).card ≤ (primeFactorsIn P m).card + 1 := by
  classical
  have hsub : primeFactorsIn P (p * m) ⊆ insert p (primeFactorsIn P m) := by
    intro q hq
    rw [mem_primeFactorsIn] at hq
    by_cases hqp : q = p
    · exact Finset.mem_insert.mpr (Or.inl hqp)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [mem_primeFactorsIn]
      refine ⟨hq.1, ?_⟩
      rcases (Nat.Prime.dvd_mul (hPprime q hq.1)).mp hq.2 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (hPprime q hq.1) hp).mp h) hqp
      · exact h
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- **The Ramaré weight caps a fibre by one.**  For `n` fixed, the designated primes `p ∣ n` with
cofactor `m = n/p` carry `‖μ(p)·c_m‖ ≤ 1/(ω_P(m)+1) ≤ 1/ω_P(n)`, and there are at most `ω_P(n)`
of them. -/
theorem norm_moebius_mul_ramareCofactorCoeff_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    ‖((μ p : ℤ) : ℂ) * ramareCofactorCoeff P m‖
      ≤ 1 / ((primeFactorsIn P (p * m)).card : ℝ) := by
  have hpp := hPprime p hp
  have hω : 1 ≤ (primeFactorsIn P (p * m)).card := by
    refine Finset.card_pos.mpr ⟨p, ?_⟩
    rw [mem_primeFactorsIn]
    exact ⟨hp, dvd_mul_right p m⟩
  have hle := card_primeFactorsIn_mul_le hPprime hpp m
  have hμp : ‖((μ p : ℤ) : ℂ)‖ ≤ 1 := by
    rw [ArithmeticFunction.moebius_apply_prime hpp]; simp
  have hc : ‖ramareCofactorCoeff P m‖ ≤ 1 / (((primeFactorsIn P m).card : ℝ) + 1) := by
    rw [ramareCofactorCoeff, norm_div]
    have hden : ‖(((primeFactorsIn P m).card : ℂ) + 1)‖ = ((primeFactorsIn P m).card : ℝ) + 1 := by
      rw [show (((primeFactorsIn P m).card : ℂ) + 1) = ((((primeFactorsIn P m).card : ℝ) + 1 : ℝ) : ℂ)
        by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hden]
    have hμm : ‖((μ m : ℤ) : ℂ)‖ ≤ 1 := by
      have h := abs_moebius_real_le_one m
      rw [show (((μ m : ℤ)) : ℂ) = ((((μ m : ℤ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact h
    exact div_le_div_of_nonneg_right hμm (by positivity)
  have hωR : ((primeFactorsIn P (p * m)).card : ℝ) ≤ ((primeFactorsIn P m).card : ℝ) + 1 := by
    exact_mod_cast hle
  have hω0 : (0 : ℝ) < ((primeFactorsIn P (p * m)).card : ℝ) := by exact_mod_cast hω
  rw [norm_mul]
  calc ‖((μ p : ℤ) : ℂ)‖ * ‖ramareCofactorCoeff P m‖
      ≤ 1 * (1 / (((primeFactorsIn P m).card : ℝ) + 1)) :=
        mul_le_mul hμp hc (norm_nonneg _) zero_le_one
    _ ≤ 1 / ((primeFactorsIn P (p * m)).card : ℝ) := by
        rw [one_mul]
        exact one_div_le_one_div_of_le hω0 hωR

/-- Reciprocal squares of integers `≥ K ≥ 2` sum to at most `1/(K-1)`. -/
theorem sum_one_div_sq_le_of_ge {s : Finset ℕ} {K : ℕ} (hK : 2 ≤ K) (hs : ∀ d ∈ s, K ≤ d) :
    ∑ d ∈ s, 1 / (d : ℝ) ^ (2 : ℕ) ≤ 1 / ((K : ℝ) - 1) := by
  classical
  -- the telescoping sum over `[K, D]`
  have htel : ∀ D : ℕ, K ≤ D + 1 →
      ∑ d ∈ Finset.Icc K D, (1 / ((d : ℝ) - 1) - 1 / (d : ℝ))
        = 1 / ((K : ℝ) - 1) - 1 / (D : ℝ) := by
    intro D hD
    induction D with
    | zero => omega
    | succ D ih =>
      rcases Nat.lt_or_ge (D + 1) K with h | h
      · have hK' : K = D + 2 := by omega
        subst hK'
        simp
        ring
      · rw [Finset.sum_Icc_succ_top h, ih (by omega)]
        push_cast
        ring
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ d ∈ s, d ≤ D := ⟨s.sup id, fun d hd => Finset.le_sup (f := id) hd⟩
  have hsub : s ⊆ Finset.Icc K (max D K) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨hs d hd, (hD d hd).trans (le_max_left _ _)⟩
  have hterm : ∀ d ∈ Finset.Icc K (max D K), 1 / (d : ℝ) ^ (2 : ℕ) ≤ 1 / ((d : ℝ) - 1) - 1 / (d : ℝ) := by
    intro d hd
    have hd2 : (2 : ℝ) ≤ d := by
      have := (Finset.mem_Icc.mp hd).1
      exact_mod_cast hK.trans this
    rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  have hnn : ∀ d ∈ Finset.Icc K (max D K), 0 ≤ 1 / (d : ℝ) ^ (2 : ℕ) := fun d _ => by positivity
  calc ∑ d ∈ s, 1 / (d : ℝ) ^ (2 : ℕ)
      ≤ ∑ d ∈ Finset.Icc K (max D K), 1 / (d : ℝ) ^ (2 : ℕ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => hnn d hd
    _ ≤ ∑ d ∈ Finset.Icc K (max D K), (1 / ((d : ℝ) - 1) - 1 / (d : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 1 / ((K : ℝ) - 1) - 1 / ((max D K : ℕ) : ℝ) := htel _ (by omega)
    _ ≤ 1 / ((K : ℝ) - 1) := by
        have : (0 : ℝ) ≤ 1 / ((max D K : ℕ) : ℝ) := by positivity
        linarith


/-! ### The ladder error as two fibred sums -/

/-- The index triple `⟨j, p, m⟩` of a ladder step, a designated prime and a cofactor. -/
abbrev LadderTriple := Σ _ : ℕ, Σ _ : ℕ, ℕ

/-- The boundary triples: `p` in the `j`-th block, `m` in the common cofactor block, `M < pm`. -/
def ladderBoundaryIndex (P : Finset ℕ) (M : ℕ) (Q η : ℝ) (L : ℕ) : Finset LadderTriple :=
  (Finset.range L).sigma fun j => (geomBlock P Q (1 + η) j).sigma fun p =>
    (geomCofactorBlock M Q η j).filter fun m => M < p * m

/-- The square triples: `p` in the `j`-th block, `m` in the common cofactor block, `pm ≤ M`,
`p ∣ m`. -/
def ladderSquareIndex (P : Finset ℕ) (M : ℕ) (Q η : ℝ) (L : ℕ) : Finset LadderTriple :=
  (Finset.range L).sigma fun j => (geomBlock P Q (1 + η) j).sigma fun p =>
    (geomCofactorBlock M Q η j).filter fun m => p * m ≤ M ∧ p ∣ m

/-- The coefficient `μ(p)·μ(m)/(ω_P(m)+1)` of a triple. -/
def ladderTripleCoeff (P : Finset ℕ) (t : LadderTriple) : ℂ :=
  ((μ t.2.1 : ℤ) : ℂ) * ramareCofactorCoeff P t.2.2

/-- The product `pm` of a triple. -/
def ladderTripleProd (t : LadderTriple) : ℕ := t.2.1 * t.2.2

/-- A cofactor of the common block is positive. -/
theorem pos_of_mem_geomCofactorBlock {M : ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {j m : ℕ}
    (hm : m ∈ geomCofactorBlock M Q η j) : 0 < m := by
  rw [geomCofactorBlock, Finset.mem_Icc] at hm
  have hpos : (0 : ℝ) < ((1 : ℕ) : ℝ) / ((Q * (1 + η) ^ j) * (1 + η)) := by
    have : (0 : ℝ) < 1 + η := by linarith
    positivity
  have := Nat.ceil_pos.mpr hpos
  omega

/-- For `p` in the `j`-th block, the designated cofactors of `p` are exactly the common block's
cofactors with `pm ≤ M`, `p ∤ m`. -/
theorem cofactorSet_eq_filter_geomCofactorBlock {P : Finset ℕ} {M : ℕ} {Q η : ℝ} (hQ : 0 < Q)
    (hη : 0 ≤ η) {j p : ℕ} (hp : p ∈ geomBlock P Q (1 + η) j) (hp0 : 0 < p) :
    {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}
      = (geomCofactorBlock M Q η j).filter fun m => p * m ≤ M ∧ ¬ p ∣ m := by
  classical
  rw [geomBlock, Finset.mem_filter] at hp
  obtain ⟨-, hlo, hhi⟩ := hp
  have hS : 0 < Q * (1 + η) ^ j := by
    have : (0 : ℝ) < 1 + η := by linarith
    positivity
  ext m
  simp only [Finset.mem_filter, mem_ramareCofactorSet_iff hp0, Finset.mem_Icc, geomCofactorBlock]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at h1
      · exact h
    refine ⟨⟨?_, ?_⟩, h2, h3⟩
    · have hle : ((1 : ℕ) : ℝ) / ((Q * (1 + η) ^ j) * (1 + η)) ≤ 1 := by
        rw [div_le_one (by have : (0 : ℝ) < 1 + η := by linarith
                           positivity)]
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
        have hsucc : Q * (1 + η) ^ (j + 1) = Q * (1 + η) ^ j * (1 + η) := by ring
        push_cast
        linarith
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      exact Nat.ceil_le.mpr (hle.trans hm1')
    · refine Nat.le_floor ?_
      rw [le_div_iff₀ hS]
      have h2' : (p : ℝ) * m ≤ M := by exact_mod_cast h2
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
  · rintro ⟨⟨h1, -⟩, h2, h3⟩
    have hm0 : 0 < m := by
      have hpos : (0 : ℝ) < ((1 : ℕ) : ℝ) / ((Q * (1 + η) ^ j) * (1 + η)) := by
        have : (0 : ℝ) < 1 + η := by linarith
        positivity
      have := Nat.ceil_pos.mpr hpos
      omega
    exact ⟨⟨Nat.mul_pos hp0 hm0, h2⟩, h3⟩

/-- The Dirichlet polynomial as a sum of phases. -/
theorem logPoly_eq_sum_mul_unitLogPhase (a : ℕ → ℂ) (s : Finset ℕ) (w : ℝ) :
    logPoly a s w = ∑ n ∈ s, a n * unitLogPhase w n := rfl

/-- **The ladder error is minus the boundary sum minus the square sum.** -/
theorem ramareLadderError_eq_neg_add {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) (w : ℝ) :
    ramareLadderError P M Q η L w
      = -((∑ t ∈ ladderBoundaryIndex P M Q η L,
            ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t))
          + ∑ t ∈ ladderSquareIndex P M Q η L,
            ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t)) := by
  classical
  rw [ramareLadderError, ladderBoundaryIndex, ladderSquareIndex]
  simp only [Finset.sum_sigma]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpP : p ∈ P := geomBlock_subset P Q (1 + η) j hp
  have hpp := hPprime p hpP
  have hp0 : 0 < p := hpp.pos
  -- split the common cofactor block into its three parts
  have hsplit : logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w
      = ramareCofactorPoly P M p w
        + (∑ m ∈ (geomCofactorBlock M Q η j).filter (fun m => M < p * m),
            ramareCofactorCoeff P m * unitLogPhase w m)
        + ∑ m ∈ (geomCofactorBlock M Q η j).filter (fun m => p * m ≤ M ∧ p ∣ m),
            ramareCofactorCoeff P m * unitLogPhase w m := by
    rw [ramareCofactorPoly, cofactorSet_eq_filter_geomCofactorBlock hQ hη hp hp0,
      logPoly_eq_sum_mul_unitLogPhase, logPoly_eq_sum_mul_unitLogPhase,
      ← Finset.sum_filter_add_sum_filter_not (geomCofactorBlock M Q η j) (fun m => p * m ≤ M),
      ← Finset.sum_filter_add_sum_filter_not
        ((geomCofactorBlock M Q η j).filter fun m => p * m ≤ M) (fun m => p ∣ m),
      Finset.filter_filter, Finset.filter_filter]
    have hB : (geomCofactorBlock M Q η j).filter (fun m => ¬ p * m ≤ M)
        = (geomCofactorBlock M Q η j).filter (fun m => M < p * m) :=
      Finset.filter_congr fun m _ => not_le
    rw [hB]
    ring
  rw [hsplit]
  have hphase : ∀ m ∈ geomCofactorBlock M Q η j,
      moebiusPhase w p * (ramareCofactorCoeff P m * unitLogPhase w m)
        = ladderTripleCoeff P ⟨j, ⟨p, m⟩⟩ * unitLogPhase w (ladderTripleProd ⟨j, ⟨p, m⟩⟩) := by
    intro m hm
    have hm0 := pos_of_mem_geomCofactorBlock hQ hη hm
    rw [ladderTripleCoeff, ladderTripleProd, moebiusPhase,
      unitLogPhase_mul w hp0.ne' hm0.ne']
    ring
  rw [show ∀ a b c : ℂ, moebiusPhase w p * (a - (a + b + c)) = -(moebiusPhase w p * b
      + moebiusPhase w p * c) from fun a b c => by ring, Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun m hm => hphase m (Finset.mem_filter.mp hm).1
  · exact Finset.sum_congr rfl fun m hm => hphase m (Finset.mem_filter.mp hm).1

/-- Two triples of the same block ladder with the same prime and the same product coincide. -/
theorem ladderTriple_eq_of_prime_eq {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    {t t' : LadderTriple} (hj : t.1 ∈ Finset.range L) (hj' : t'.1 ∈ Finset.range L)
    (hp : t.2.1 ∈ geomBlock P Q (1 + η) t.1) (hp' : t'.2.1 ∈ geomBlock P Q (1 + η) t'.1)
    (hp0 : 0 < t.2.1) (hprod : ladderTripleProd t = ladderTripleProd t')
    (hpp : t.2.1 = t'.2.1) : t = t' := by
  obtain ⟨j, p, m⟩ := t
  obtain ⟨j', p', m'⟩ := t'
  simp only at hj hj' hp hp' hp0 hpp
  subst hpp
  have hm : m = m' := by
    simp only [ladderTripleProd] at hprod
    exact Nat.eq_of_mul_eq_mul_left hp0 hprod
  subst hm
  have hjj : j = j' := by
    by_contra hne
    have hdisj := geomBlock_pairwiseDisjoint P hQ (by linarith : (1 : ℝ) ≤ 1 + η) L
      (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hj') hne
    exact Finset.disjoint_left.mp hdisj hp hp'
  subst hjj
  rfl

/-- **The boundary part of the ladder error has energy at most `ηM`.** -/
theorem integral_normSq_ladderBoundary_le {P : Finset ℕ} (M : ℕ) {Q η W : ℝ} (hQ : 0 < Q)
    (hη : 0 ≤ η) (hW : 1 ≤ W) (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) :
    (∫ w in Set.Icc (-W) W, ‖∑ t ∈ ladderBoundaryIndex P M Q η L,
        ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t)‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (η * M) := by
  classical
  have hmem : ∀ t ∈ ladderBoundaryIndex P M Q η L, t.1 ∈ Finset.range L ∧
      t.2.1 ∈ geomBlock P Q (1 + η) t.1 ∧ t.2.2 ∈ geomCofactorBlock M Q η t.1
        ∧ M < t.2.1 * t.2.2 := by
    intro t ht
    simp only [ladderBoundaryIndex, Finset.mem_sigma, Finset.mem_filter] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
  -- products lie in `(M, M(1+η)]`
  have hrange : ∀ t ∈ ladderBoundaryIndex P M Q η L,
      M < ladderTripleProd t ∧ ladderTripleProd t ≤ ⌊(M : ℝ) * (1 + η)⌋₊ := by
    intro t ht
    obtain ⟨-, hp, hm, hlt⟩ := hmem t ht
    refine ⟨hlt, Nat.le_floor ?_⟩
    rw [geomBlock, Finset.mem_filter] at hp
    rw [geomCofactorBlock, Finset.mem_Icc] at hm
    have hS : 0 < Q * (1 + η) ^ t.1 := by
      have : (0 : ℝ) < 1 + η := by linarith
      positivity
    have hmle : (t.2.2 : ℝ) ≤ (M : ℝ) / (Q * (1 + η) ^ t.1) :=
      (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by positivity))
    have hm0 : (0 : ℝ) ≤ t.2.2 := Nat.cast_nonneg _
    rw [ladderTripleProd]
    push_cast
    calc (t.2.1 : ℝ) * t.2.2 ≤ (Q * (1 + η) ^ t.1 * (1 + η)) * ((M : ℝ) / (Q * (1 + η) ^ t.1)) := by
          have h1 := hp.2.2
          rw [pow_succ] at h1
          gcongr
          linarith
      _ = (M : ℝ) * (1 + η) := by field_simp
  -- one unit per fibre
  have hfib : ∀ n, ∑ t ∈ ladderBoundaryIndex P M Q η L with ladderTripleProd t = n,
      ‖ladderTripleCoeff P t‖ ≤ 1 := by
    intro n
    set F := (ladderBoundaryIndex P M Q η L).filter fun t => ladderTripleProd t = n with hF
    have hterm : ∀ t ∈ F, ‖ladderTripleCoeff P t‖ ≤ 1 / ((primeFactorsIn P n).card : ℝ) := by
      intro t ht
      obtain ⟨htI, htn⟩ := Finset.mem_filter.mp ht
      obtain ⟨-, hp, -, -⟩ := hmem t htI
      rw [← htn, ladderTripleProd]
      exact norm_moebius_mul_ramareCofactorCoeff_le hPprime (geomBlock_subset P Q (1 + η) _ hp) _
    have hcard : F.card ≤ (primeFactorsIn P n).card := by
      refine Finset.card_le_card_of_injOn (fun t => t.2.1) (fun t ht => ?_) (fun t ht t' ht' h => ?_)
      · obtain ⟨htI, htn⟩ := Finset.mem_filter.mp ht
        obtain ⟨-, hp, -, -⟩ := hmem t htI
        rw [Finset.mem_coe, mem_primeFactorsIn]
        refine ⟨geomBlock_subset P Q (1 + η) _ hp, ?_⟩
        rw [← htn, ladderTripleProd]
        exact dvd_mul_right _ _
      · obtain ⟨htI, htn⟩ := Finset.mem_filter.mp ht
        obtain ⟨htI', htn'⟩ := Finset.mem_filter.mp ht'
        obtain ⟨hj, hp, -, -⟩ := hmem t htI
        obtain ⟨hj', hp', -, -⟩ := hmem t' htI'
        have hp0 : 0 < t.2.1 := (hPprime _ (geomBlock_subset P Q (1 + η) _ hp)).pos
        exact ladderTriple_eq_of_prime_eq hQ hη hj hj' hp hp' hp0 (htn.trans htn'.symm) h
    calc ∑ t ∈ F, ‖ladderTripleCoeff P t‖ ≤ ∑ _t ∈ F, 1 / ((primeFactorsIn P n).card : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (F.card : ℝ) * (1 / ((primeFactorsIn P n).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((primeFactorsIn P n).card : ℝ) * (1 / ((primeFactorsIn P n).card : ℝ)) := by
          gcongr
      _ ≤ 1 := by
          rcases Nat.eq_zero_or_pos (primeFactorsIn P n).card with h | h
          · rw [h]; simp
          · rw [mul_one_div_cancel (by exact_mod_cast h.ne')]
  have hbase := integral_normSq_sum_unitLogPhase_le (ladderBoundaryIndex P M Q η L)
    ladderTripleProd (ladderTripleCoeff P) (fun t ht => by have := (hrange t ht).1; omega)
    (fun t ht => (hrange t ht).2) hW
  have henergy := sum_normSq_fibre_le_card (ladderBoundaryIndex P M Q η L) ladderTripleProd
    (ladderTripleCoeff P) hfib
  -- the image has at most `ηM` elements
  have himg : (((ladderBoundaryIndex P M Q η L).image ladderTripleProd).card : ℝ) ≤ η * M := by
    have hsub : (ladderBoundaryIndex P M Q η L).image ladderTripleProd
        ⊆ Finset.Ioc M ⌊(M : ℝ) * (1 + η)⌋₊ := by
      intro n hn
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Ioc.mpr (hrange t ht)
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at hc
    have hfl : ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) ≤ (M : ℝ) * (1 + η) :=
      Nat.floor_le (by positivity)
    have hc' : (((ladderBoundaryIndex P M Q η L).image ladderTripleProd).card : ℝ)
        ≤ ((⌊(M : ℝ) * (1 + η)⌋₊ - M : ℕ) : ℝ) := by exact_mod_cast hc
    refine hc'.trans ?_
    rcases le_total M ⌊(M : ℝ) * (1 + η)⌋₊ with h | h
    · rw [Nat.cast_sub h]; linarith
    · rw [Nat.sub_eq_zero_of_le h]; simp; positivity
  have hcoef : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left (henergy.trans himg) hcoef)

/-- **Square-divisor multiplicities.**  For a set `P` of primes,
`∑_{n ≤ M} #{p ∈ P : p² ∣ n}² ≤ M(s + s²)`, `s = ∑_{p ∈ P} 1/p²`. -/
theorem sum_sq_card_sqDivisors_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (((P.filter fun p => p ^ 2 ∣ n).card : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ (M : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
        + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  classical
  -- counting multiples
  have hmult : ∀ d : ℕ, 1 ≤ d →
      (((Finset.Icc 1 M).filter fun n => d ∣ n).card : ℝ) ≤ (M : ℝ) / d := by
    intro d hd
    have h := sum_filter_dvd_eq (M := M) hd (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, add_tsub_cancel_right] at h
    rw [h]
    exact Nat.cast_div_le
  have hexp : ∀ n, (((P.filter fun p => p ^ 2 ∣ n).card : ℕ) : ℝ) ^ (2 : ℕ)
      = ∑ p ∈ P, ∑ q ∈ P, (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases hp : p ^ 2 ∣ n <;> by_cases hq : q ^ 2 ∣ n <;> simp [hp, hq]
  simp_rw [hexp]
  have hpair : ∀ p ∈ P, ∀ q ∈ P, ∑ n ∈ Finset.Icc 1 M,
      (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0)
        ≤ (if p = q then (M : ℝ) / (p : ℝ) ^ (2 : ℕ) else 0)
          + (M : ℝ) * (1 / (p : ℝ) ^ (2 : ℕ)) * (1 / (q : ℝ) ^ (2 : ℕ)) := by
    intro p hp q hq
    have hpp := hPprime p hp
    have hqq := hPprime q hq
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases hpq : p = q
    · subst hpq
      simp only [and_self, if_true]
      have := hmult (p ^ 2) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpp.ne_zero))
      push_cast at this
      have h0 : (0 : ℝ) ≤ (M : ℝ) * (1 / (p : ℝ) ^ (2 : ℕ)) * (1 / (p : ℝ) ^ (2 : ℕ)) := by
        positivity
      linarith
    · simp only [hpq, if_false, zero_add]
      have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
        Nat.Coprime.pow 2 2 ((Nat.coprime_primes hpp hqq).mpr hpq)
      have hsub : (Finset.Icc 1 M).filter (fun n => p ^ 2 ∣ n ∧ q ^ 2 ∣ n)
          = (Finset.Icc 1 M).filter (fun n => p ^ 2 * q ^ 2 ∣ n) :=
        Finset.filter_congr fun n _ => ⟨fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2,
          fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩⟩
      rw [hsub]
      have := hmult (p ^ 2 * q ^ 2) (Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero 2 hpp.ne_zero) (pow_ne_zero 2 hqq.ne_zero)))
      push_cast at this
      calc _ ≤ (M : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := this
        _ = _ := by field_simp
  calc ∑ n ∈ Finset.Icc 1 M, ∑ p ∈ P, ∑ q ∈ P,
        (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0)
      = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 M,
          (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((if p = q then (M : ℝ) / (p : ℝ) ^ (2 : ℕ) else 0)
          + (M : ℝ) * (1 / (p : ℝ) ^ (2 : ℕ)) * (1 / (q : ℝ) ^ (2 : ℕ))) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hpair p hp q hq
    _ = (M : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
          + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
        simp only [Finset.sum_add_distrib]
        rw [mul_add]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.sum_ite_eq, if_pos hp]
          ring
        · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring

/-- **The square part of the ladder error.**  Its products are divisible by `p²` for a designated
prime `p`, so its energy is at most `M(s + s²)`, `s = ∑_{p ∈ P} 1/p²`. -/
theorem integral_normSq_ladderSquare_le {P : Finset ℕ} (M : ℕ) {Q η W : ℝ} (hQ : 0 < Q)
    (hη : 0 ≤ η) (hW : 1 ≤ W) (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) :
    (∫ w in Set.Icc (-W) W, ‖∑ t ∈ ladderSquareIndex P M Q η L,
        ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t)‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((M : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
            + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ))) := by
  classical
  have hmem : ∀ t ∈ ladderSquareIndex P M Q η L, t.1 ∈ Finset.range L ∧
      t.2.1 ∈ geomBlock P Q (1 + η) t.1 ∧ t.2.2 ∈ geomCofactorBlock M Q η t.1
        ∧ t.2.1 * t.2.2 ≤ M ∧ t.2.1 ∣ t.2.2 := by
    intro t ht
    simp only [ladderSquareIndex, Finset.mem_sigma, Finset.mem_filter] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
  have hpos : ∀ t ∈ ladderSquareIndex P M Q η L, 0 < ladderTripleProd t := by
    intro t ht
    obtain ⟨-, hp, hm, -, -⟩ := hmem t ht
    exact Nat.mul_pos (hPprime _ (geomBlock_subset P Q (1 + η) _ hp)).pos
      (pos_of_mem_geomCofactorBlock hQ hη hm)
  have hbase := integral_normSq_sum_unitLogPhase_le (ladderSquareIndex P M Q η L)
    ladderTripleProd (ladderTripleCoeff P) hpos (fun t ht => (hmem t ht).2.2.2.1) hW
  -- each fibre is bounded by the number of designated square divisors
  have hfib : ∀ n, ‖∑ t ∈ ladderSquareIndex P M Q η L with ladderTripleProd t = n,
      ladderTripleCoeff P t‖ ≤ (((P.filter fun p => p ^ 2 ∣ n).card : ℕ) : ℝ) := by
    intro n
    set F := (ladderSquareIndex P M Q η L).filter fun t => ladderTripleProd t = n
    have hterm : ∀ t ∈ F, ‖ladderTripleCoeff P t‖ ≤ 1 := by
      intro t ht
      obtain ⟨htI, -⟩ := Finset.mem_filter.mp ht
      obtain ⟨-, hp, -, -, -⟩ := hmem t htI
      have hpP := geomBlock_subset P Q (1 + η) _ hp
      refine (norm_moebius_mul_ramareCofactorCoeff_le hPprime hpP _).trans ?_
      have hω : 1 ≤ (primeFactorsIn P (t.2.1 * t.2.2)).card :=
        Finset.card_pos.mpr ⟨t.2.1, (mem_primeFactorsIn).mpr ⟨hpP, dvd_mul_right _ _⟩⟩
      have hω' : (1 : ℝ) ≤ (primeFactorsIn P (t.2.1 * t.2.2)).card := by exact_mod_cast hω
      rw [div_le_one (by linarith)]
      exact hω'
    have hcard : F.card ≤ (P.filter fun p => p ^ 2 ∣ n).card := by
      refine Finset.card_le_card_of_injOn (fun t => t.2.1) (fun t ht => ?_) (fun t ht t' ht' h => ?_)
      · obtain ⟨htI, htn⟩ := Finset.mem_filter.mp ht
        obtain ⟨-, hp, -, -, hdvd⟩ := hmem t htI
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨geomBlock_subset P Q (1 + η) _ hp, ?_⟩
        rw [← htn, ladderTripleProd, sq]
        exact Nat.mul_dvd_mul_left _ hdvd
      · obtain ⟨htI, htn⟩ := Finset.mem_filter.mp ht
        obtain ⟨htI', htn'⟩ := Finset.mem_filter.mp ht'
        obtain ⟨hj, hp, -, -, -⟩ := hmem t htI
        obtain ⟨hj', hp', -, -, -⟩ := hmem t' htI'
        have hp0 : 0 < t.2.1 := (hPprime _ (geomBlock_subset P Q (1 + η) _ hp)).pos
        exact ladderTriple_eq_of_prime_eq hQ hη hj hj' hp hp' hp0 (htn.trans htn'.symm) h
    calc ‖∑ t ∈ F, ladderTripleCoeff P t‖ ≤ ∑ t ∈ F, ‖ladderTripleCoeff P t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ F, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := by exact_mod_cast hcard
  have himg : (ladderSquareIndex P M Q η L).image ladderTripleProd ⊆ Finset.Icc 1 M := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨hpos t ht, (hmem t ht).2.2.2.1⟩
  have henergy : ∑ n ∈ (ladderSquareIndex P M Q η L).image ladderTripleProd,
      ‖∑ t ∈ ladderSquareIndex P M Q η L with ladderTripleProd t = n, ladderTripleCoeff P t‖ ^ (2 : ℕ)
        ≤ (M : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
          + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
    refine le_trans ?_ (sum_sq_card_sqDivisors_le hPprime M)
    calc _ ≤ ∑ n ∈ (ladderSquareIndex P M Q η L).image ladderTripleProd,
          (((P.filter fun p => p ^ 2 ∣ n).card : ℕ) : ℝ) ^ (2 : ℕ) :=
          Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hfib n) 2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
  have hcoef : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left henergy hcoef)

/-- **The sharp ladder error.**  For a set `P` of primes above `Q ≥ 1`,
`∫_{|w| ≤ W} ‖ladder error‖² ≤ 2(5π/2·W + 5e/2·⌊M(1+η)⌋)·(ηM + 6M/Q)`. -/
theorem integral_normSq_ramareLadderError_le_sharp {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime)
    (hPgt : ∀ p ∈ P, Q < (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ))
      ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (η * M + 6 * M / Q) := by
  classical
  have hQ0 : (0 : ℝ) < Q := by linarith
  set A : ℝ → ℂ := fun w => ∑ t ∈ ladderBoundaryIndex P M Q η L,
    ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t) with hA
  set B : ℝ → ℂ := fun w => ∑ t ∈ ladderSquareIndex P M Q η L,
    ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t) with hB
  have hcont : ∀ (I : Finset LadderTriple), Continuous fun w : ℝ =>
      ∑ t ∈ I, ladderTripleCoeff P t * unitLogPhase w (ladderTripleProd t) := fun I =>
    continuous_finsetSum _ fun t _ => continuous_const.mul (continuous_unitLogPhase _)
  have hpt : ∀ w, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ)
      ≤ 2 * ‖A w‖ ^ (2 : ℕ) + 2 * ‖B w‖ ^ (2 : ℕ) := by
    intro w
    rw [ramareLadderError_eq_neg_add M hQ0 hη L hPprime w, norm_neg]
    have h := norm_add_le (A w) (B w)
    nlinarith [norm_nonneg (A w), norm_nonneg (B w), norm_nonneg (A w + B w),
      sq_nonneg (‖A w‖ - ‖B w‖)]
  have hintE : IntegrableOn (fun w => ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) := ((continuous_ramareLadderError P M Q η L).norm.pow 2).integrableOn_Icc
  have hintA : IntegrableOn (fun w => ‖A w‖ ^ (2 : ℕ)) (Set.Icc (-W) W) :=
    ((hcont _).norm.pow 2).integrableOn_Icc
  have hintB : IntegrableOn (fun w => ‖B w‖ ^ (2 : ℕ)) (Set.Icc (-W) W) :=
    ((hcont _).norm.pow 2).integrableOn_Icc
  have hint2 : IntegrableOn (fun w => 2 * ‖A w‖ ^ (2 : ℕ) + 2 * ‖B w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) := (hintA.const_mul 2).add (hintB.const_mul 2)
  have hmono := setIntegral_mono_on hintE hint2 measurableSet_Icc fun w _ => hpt w
  rw [integral_add (hintA.const_mul 2) (hintB.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  have h1 := integral_normSq_ladderBoundary_le M hQ0 hη hW L hPprime
  have h2 := integral_normSq_ladderSquare_le M hQ0 hη hW L hPprime
  -- the reciprocal-square mass of the designated primes
  have hK : 2 ≤ ⌊Q⌋₊ + 1 := by
    have : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
    omega
  have hs : ∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ) ≤ 2 / Q := by
    refine (sum_one_div_sq_le_of_ge hK fun p hp => ?_).trans ?_
    · exact Nat.succ_le_of_lt ((Nat.floor_lt (by linarith)).mpr (hPgt p hp))
    · push_cast
      have hfl : Q / 2 ≤ (⌊Q⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one Q
        have h1 : (1 : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hQ)
        linarith
      rw [add_sub_cancel_right, div_le_div_iff₀ (by linarith) hQ0]
      linarith
  have hs0 : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ) := Finset.sum_nonneg fun p _ => by positivity
  have hs1 : ∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ) ≤ 2 := hs.trans (by
    rw [div_le_iff₀ hQ0]; linarith)
  have hsq : (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)
      ≤ 3 * (2 / Q) := by nlinarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN : (M : ℝ) ≤ ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_floor (by nlinarith)
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have haff0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    positivity
  have haff : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)
      ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    have := (Real.exp_pos 1).le
    nlinarith
  have hMs : (M : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
      + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) ≤ 6 * M / Q := by
    calc _ ≤ (M : ℝ) * (3 * (2 / Q)) := mul_le_mul_of_nonneg_left hsq hM0
      _ = 6 * M / Q := by ring
  have hE2 : 0 ≤ (M : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ))
      + (∑ p ∈ P, 1 / (p : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) := by positivity
  have h2' := h2.trans (mul_le_mul haff hMs hE2 (haff0.trans haff))
  have hηM : 0 ≤ η * M := by positivity
  calc (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in Set.Icc (-W) W, ‖A w‖ ^ (2 : ℕ))
          + 2 * (∫ w in Set.Icc (-W) W, ‖B w‖ ^ (2 : ℕ)) := hmono
    _ ≤ _ := by nlinarith [h1, h2']

end

end RHTower.Sieve
