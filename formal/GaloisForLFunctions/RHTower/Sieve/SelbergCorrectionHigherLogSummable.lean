import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerGlobalIdentity

/-!
# Absolute summability of every global logarithmic correction jet

Differentiating the finite Euler product marks one prime and removes its complete prime-power
fibre.  The resulting exact recurrence, together with the all-order local `p⁻² log(p)^k`
majorants, proves absolute summability by strong induction on derivative order.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private theorem derivative_finset_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → PowerSeries ℝ) :
    PowerSeries.derivative ℝ (∏ x ∈ s, f x) =
      ∑ x ∈ s, PowerSeries.derivative ℝ (f x) * ∏ y ∈ s.erase x, f y := by
  induction s using Finset.induction_on with
  | empty => simp [Derivation.map_one_eq_zero]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [Finset.sum_insert ha]
      rw [Finset.erase_insert ha]
      rw [ih]
      rw [Finset.mul_sum]
      calc
        (∑ x ∈ s, f a *
              (PowerSeries.derivative ℝ (f x) * ∏ y ∈ s.erase x, f y)) +
            (∏ y ∈ s, f y) * PowerSeries.derivative ℝ (f a) =
            (∏ y ∈ s, f y) * PowerSeries.derivative ℝ (f a) +
              ∑ x ∈ s, f a *
                (PowerSeries.derivative ℝ (f x) * ∏ y ∈ s.erase x, f y) := by ring
        _ = _ := by
          apply congrArg₂ (· + ·)
          · ring
          · apply Finset.sum_congr rfl
            intro x hx
            have hax : a ≠ x := by
              intro h
              subst x
              exact ha hx
            rw [Finset.erase_insert_of_ne hax,
              Finset.prod_insert (by simp [ha])]
            ring

private theorem pair_ordCompl_primeFactors
    {m n p : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hp : p ∈ (m * n).primeFactors) :
    ((m / p ^ m.factorization p) * (n / p ^ n.factorization p)).primeFactors =
      (m * n).primeFactors.erase p := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hm' : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm.ne'
  have hn' : 0 < n / p ^ n.factorization p := Nat.ordCompl_pos p hn.ne'
  have hpM : ¬ p ∣ m / p ^ m.factorization p :=
    Nat.not_dvd_ordCompl hpprime hm.ne'
  have hpN : ¬ p ∣ n / p ^ n.factorization p :=
    Nat.not_dvd_ordCompl hpprime hn.ne'
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_erase]
  constructor
  · rintro ⟨hqprime, hqdiv, hrest0⟩
    have hqne : q ≠ p := by
      intro hqp
      subst q
      rcases hpprime.dvd_mul.mp hqdiv with hpm | hpn
      · exact hpM hpm
      · exact hpN hpn
    have hmdiv : m / p ^ m.factorization p ∣ m :=
      Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p)
    have hndiv : n / p ^ n.factorization p ∣ n :=
      Nat.div_dvd_of_dvd (Nat.ordProj_dvd n p)
    exact ⟨hqne, hqprime, dvd_trans hqdiv (mul_dvd_mul hmdiv hndiv),
      Nat.mul_ne_zero hm.ne' hn.ne'⟩
  · rintro ⟨hqne, hqprime, hqdiv, hmn0⟩
    have hqpow : ∀ a : ℕ, ¬ q ∣ p ^ a := by
      intro a hdiv
      have hqp : q ∣ p := hqprime.dvd_of_dvd_pow hdiv
      exact hqne ((Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hqp)
    have hreconM : p ^ m.factorization p * (m / p ^ m.factorization p) = m :=
      Nat.ordProj_mul_ordCompl_eq_self m p
    have hreconN : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hqrest : q ∣ (m / p ^ m.factorization p) *
        (n / p ^ n.factorization p) := by
      rcases hqprime.dvd_mul.mp hqdiv with hqm | hqn
      · rw [← hreconM] at hqm
        rcases hqprime.dvd_mul.mp hqm with hqpa | hqm'
        · exact (hqpow _ hqpa).elim
        · exact hqm'.mul_right _
      · rw [← hreconN] at hqn
        rcases hqprime.dvd_mul.mp hqn with hqpa | hqn'
        · exact (hqpow _ hqpa).elim
        · exact hqn'.mul_left _
    exact ⟨hqprime, hqrest, Nat.mul_ne_zero hm'.ne' hn'.ne'⟩

private theorem factorization_ordCompl_of_ne
    {m p q : ℕ} (hm : 0 < m) (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) :
    (m / p ^ m.factorization p).factorization q = m.factorization q := by
  have hm' : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm.ne'
  have hqpow : ¬ q ∣ p ^ m.factorization p := by
    intro hdiv
    have hqd : q ∣ p := hq.dvd_of_dvd_pow hdiv
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqd)
  have hrecon : p ^ m.factorization p * (m / p ^ m.factorization p) = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  calc
    (m / p ^ m.factorization p).factorization q =
        0 + (m / p ^ m.factorization p).factorization q := by simp
    _ = (p ^ m.factorization p).factorization q +
        (m / p ^ m.factorization p).factorization q := by
      rw [Nat.factorization_eq_zero_of_not_dvd hqpow]
    _ = (p ^ m.factorization p *
          (m / p ^ m.factorization p)).factorization q := by
      have hfac := congrArg (fun f => f q)
        (Nat.factorization_mul
          (a := p ^ m.factorization p)
          (b := m / p ^ m.factorization p)
          (pow_ne_zero _ hp.ne_zero) hm'.ne')
      simpa using hfac.symm
    _ = m.factorization q := by rw [hrecon]

private theorem selbergEulerCorrectionJet_prod_erase_eq
    {m n p : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hp : p ∈ (m * n).primeFactors) :
    (∏ q ∈ (m * n).primeFactors.erase p,
        selbergCorrectionJetLocal q (m.factorization q) (n.factorization q)) =
      selbergEulerCorrectionJet
        (m / p ^ m.factorization p) (n / p ^ n.factorization p) := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hm' : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm.ne'
  have hn' : 0 < n / p ^ n.factorization p := Nat.ordCompl_pos p hn.ne'
  rw [selbergEulerCorrectionJet, if_neg (not_or_intro hm'.ne' hn'.ne'),
    pair_ordCompl_primeFactors hm hn hp]
  apply Finset.prod_congr rfl
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase hq)
  have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
  rw [factorization_ordCompl_of_ne hm hpprime hqprime hqp,
    factorization_ordCompl_of_ne hn hpprime hqprime hqp]

private theorem ordinary_coeff_derivative_selbergCorrectionJetLocal
    (r p i j : ℕ) :
    (r.factorial : ℝ) * PowerSeries.coeff r
        (PowerSeries.derivative ℝ (selbergCorrectionJetLocal p i j)) =
      selbergCorrectionLogPowerLocal (r + 1) p i j := by
  rw [PowerSeries.coeff_derivative, coeff_selbergCorrectionJetLocal_succ]
  have hfac : (((r + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Exact marked-prime recurrence for every positive-order global correction jet. -/
theorem selbergEulerCorrectionLogPowerCoeff_succ_eq
    (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    selbergEulerCorrectionLogPowerCoeff (k + 1) m n =
      ∑ p ∈ (m * n).primeFactors, ∑ r ∈ Finset.range (k + 1),
        (k.choose r : ℝ) *
          selbergCorrectionLogPowerLocal (r + 1) p
            (m.factorization p) (n.factorization p) *
          selbergEulerCorrectionLogPowerCoeff (k - r)
            (m / p ^ m.factorization p) (n / p ^ n.factorization p) := by
  rw [selbergEulerCorrectionLogPowerCoeff,
    selbergEulerCorrectionJet, if_neg (not_or_intro hm.ne' hn.ne')]
  have hderiv := derivative_finset_prod (m * n).primeFactors
    (fun p => selbergCorrectionJetLocal p (m.factorization p) (n.factorization p))
  have hcoeff := congrArg (fun F =>
    (k.factorial : ℝ) * PowerSeries.coeff k F) hderiv
  rw [map_sum, Finset.mul_sum] at hcoeff
  calc
    (((k + 1).factorial : ℕ) : ℝ) *
        PowerSeries.coeff (k + 1)
          (∏ p ∈ (m * n).primeFactors,
            selbergCorrectionJetLocal p (m.factorization p) (n.factorization p)) =
      (k.factorial : ℝ) * PowerSeries.coeff k
        (PowerSeries.derivative ℝ
          (∏ p ∈ (m * n).primeFactors,
            selbergCorrectionJetLocal p (m.factorization p) (n.factorization p))) := by
      rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
      push_cast
      ring
    _ = ∑ p ∈ (m * n).primeFactors,
        (k.factorial : ℝ) * PowerSeries.coeff k
          (PowerSeries.derivative ℝ
              (selbergCorrectionJetLocal p (m.factorization p) (n.factorization p)) *
            ∏ q ∈ (m * n).primeFactors.erase p,
              selbergCorrectionJetLocal q (m.factorization q) (n.factorization q)) := hcoeff
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ordinaryPowerSeriesCoeff_mul,
        selbergEulerCorrectionJet_prod_erase_eq hm hn hp]
      apply Finset.sum_congr rfl
      intro r hr
      rw [ordinary_coeff_derivative_selbergCorrectionJetLocal]
      rfl

private theorem selbergCorrectionLogPowerMajorant_succ_nonneg'
    (a p alpha beta : ℕ) :
    0 ≤ selbergCorrectionLogPowerMajorant (a + 1) p alpha beta := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p <;>
      simp [selbergCorrectionLogPowerMajorant, geomTailTwo, geomTailOne]
  · exact selbergCorrectionLogPowerMajorant_nonneg (a + 1) hp alpha beta

private theorem summable_selbergCorrectionLogPowerMajorant_succ'
    (a p : ℕ) :
    Summable (fun ab : ℕ × ℕ =>
      selbergCorrectionLogPowerMajorant (a + 1) p ab.1 ab.2) := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · refine summable_zero.congr ?_
    intro ab
    interval_cases p <;>
      simp [selbergCorrectionLogPowerMajorant, geomTailTwo, geomTailOne]
  · exact summable_selbergCorrectionLogPowerMajorant (a + 1) hp

private theorem tsum_selbergCorrectionLogPowerMajorant_succ_le'
    (a p : ℕ) :
    (∑' ab : ℕ × ℕ,
      selbergCorrectionLogPowerMajorant (a + 1) p ab.1 ab.2) ≤
      (8 + 4 * (2 : ℝ) ^ (a + 1)) * Real.log (p : ℝ) ^ (a + 1) /
        (p : ℝ) ^ (2 : ℕ) := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · have hzero : (fun ab : ℕ × ℕ =>
        selbergCorrectionLogPowerMajorant (a + 1) p ab.1 ab.2) = fun _ => 0 := by
      funext ab
      interval_cases p <;>
        simp [selbergCorrectionLogPowerMajorant, geomTailTwo, geomTailOne]
    rw [hzero, tsum_zero]
    interval_cases p <;> simp
  · exact tsum_selbergCorrectionLogPowerMajorant_le (a + 1) hp

private def padicLogPowerMajorantTerm (a lower p : ℕ) (mn : ℕ × ℕ) : ℝ :=
  selbergCorrectionLogPowerMajorant (a + 1) p
      (mn.1.factorization p) (mn.2.factorization p) *
    |selbergEulerCorrectionLogPowerCoeff lower
      (mn.1 / p ^ mn.1.factorization p)
      (mn.2 / p ^ mn.2.factorization p)|

private theorem padicLogPowerMajorantTerm_nonneg
    (a lower p : ℕ) (mn : ℕ × ℕ) :
    0 ≤ padicLogPowerMajorantTerm a lower p mn :=
  mul_nonneg (selbergCorrectionLogPowerMajorant_succ_nonneg' _ _ _ _) (abs_nonneg _)

private def splitLogPowerMajorant (a lower p : ℕ)
    (y : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  selbergCorrectionLogPowerMajorant (a + 1) p y.1.1 y.1.2 *
    |selbergEulerCorrectionLogPowerCoeff lower y.2.1 y.2.2|

private theorem splitLogPowerMajorant_nonneg
    (a lower p : ℕ) (y : (ℕ × ℕ) × (ℕ × ℕ)) :
    0 ≤ splitLogPowerMajorant a lower p y :=
  mul_nonneg (selbergCorrectionLogPowerMajorant_succ_nonneg' _ _ _ _) (abs_nonneg _)

private theorem summable_splitLogPowerMajorant
    (a lower p : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|)) :
    Summable (splitLogPowerMajorant a lower p) :=
  (summable_selbergCorrectionLogPowerMajorant_succ' a p).mul_of_nonneg hLower
    (fun ab => selbergCorrectionLogPowerMajorant_succ_nonneg' a p ab.1 ab.2)
    (fun _ => abs_nonneg _)

private theorem tsum_splitLogPowerMajorant_eq
    (a lower p : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|)) :
    (∑' y : (ℕ × ℕ) × (ℕ × ℕ), splitLogPowerMajorant a lower p y) =
      (∑' ab : ℕ × ℕ,
        selbergCorrectionLogPowerMajorant (a + 1) p ab.1 ab.2) *
      (∑' mn : ℕ × ℕ,
        |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|) :=
  ((summable_selbergCorrectionLogPowerMajorant_succ' a p).tsum_mul_tsum
    hLower (summable_splitLogPowerMajorant a lower p hLower)).symm

private theorem summable_padicLogPowerMajorantTerm
    (a lower p : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|)) :
    Summable (padicLogPowerMajorantTerm a lower p) := by
  refine ((summable_splitLogPowerMajorant a lower p hLower).comp_injective
    (padicSplit_injective p)).congr ?_
  intro mn
  rfl

private theorem tsum_padicLogPowerMajorantTerm_le
    (a lower p : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|)) :
    (∑' mn : ℕ × ℕ, padicLogPowerMajorantTerm a lower p mn) ≤
      ((8 + 4 * (2 : ℝ) ^ (a + 1)) * Real.log (p : ℝ) ^ (a + 1) /
          (p : ℝ) ^ (2 : ℕ)) *
        (∑' mn : ℕ × ℕ,
          |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|) := by
  refine (summable_padicLogPowerMajorantTerm a lower p hLower).tsum_le_of_sum_le ?_
  intro s
  have hinj : Set.InjOn (padicSplit p) ↑s :=
    fun x _ y _ h => padicSplit_injective p h
  have hrw : ∀ i ∈ s, padicLogPowerMajorantTerm a lower p i =
      splitLogPowerMajorant a lower p (padicSplit p i) := fun _ _ => rfl
  rw [Finset.sum_congr rfl hrw, ← Finset.sum_image hinj]
  refine le_trans ((summable_splitLogPowerMajorant a lower p hLower).sum_le_tsum _
    (fun y _ => splitLogPowerMajorant_nonneg a lower p y)) ?_
  rw [tsum_splitLogPowerMajorant_eq a lower p hLower]
  exact mul_le_mul_of_nonneg_right
    (tsum_selbergCorrectionLogPowerMajorant_succ_le' a p)
    (tsum_nonneg fun _ => abs_nonneg _)

private theorem summable_padicLogPowerMajorantProd
    (a lower : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|)) :
    Summable (fun x : ℕ × (ℕ × ℕ) =>
      padicLogPowerMajorantTerm a lower x.1 x.2) := by
  rw [summable_prod_of_nonneg
    (fun x => padicLogPowerMajorantTerm_nonneg a lower x.1 x.2)]
  refine ⟨fun p => summable_padicLogPowerMajorantTerm a lower p hLower, ?_⟩
  exact Summable.of_nonneg_of_le
    (fun p => tsum_nonneg fun mn => padicLogPowerMajorantTerm_nonneg a lower p mn)
    (fun p => tsum_padicLogPowerMajorantTerm_le a lower p hLower)
    ((summable_selbergCorrectionLogPowerPrimeBound (a + 1)).mul_right _)

private theorem summable_padicLogPowerMajorantSum
    (a lower : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|)) :
    Summable (fun mn : ℕ × ℕ =>
      ∑' p : ℕ, padicLogPowerMajorantTerm a lower p mn) := by
  have hswap : Summable (fun x : (ℕ × ℕ) × ℕ =>
      padicLogPowerMajorantTerm a lower x.2 x.1) := by
    refine ((Equiv.prodComm (ℕ × ℕ) ℕ).summable_iff
      (f := fun x : ℕ × (ℕ × ℕ) =>
        padicLogPowerMajorantTerm a lower x.1 x.2)).2
      (summable_padicLogPowerMajorantProd a lower hLower) |>.congr ?_
    intro x
    rfl
  exact ((summable_prod_of_nonneg
    (f := fun x : (ℕ × ℕ) × ℕ =>
      padicLogPowerMajorantTerm a lower x.2 x.1)
    (fun x => padicLogPowerMajorantTerm_nonneg a lower x.2 x.1)).1 hswap).2

private theorem summable_padicLogPowerMajorantTerm_fixed
    (a lower : ℕ)
    (hLower : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff lower mn.1 mn.2|))
    (mn : ℕ × ℕ) :
    Summable (fun p : ℕ => padicLogPowerMajorantTerm a lower p mn) := by
  have hswap : Summable (fun x : (ℕ × ℕ) × ℕ =>
      padicLogPowerMajorantTerm a lower x.2 x.1) := by
    refine ((Equiv.prodComm (ℕ × ℕ) ℕ).summable_iff
      (f := fun x : ℕ × (ℕ × ℕ) =>
        padicLogPowerMajorantTerm a lower x.1 x.2)).2
      (summable_padicLogPowerMajorantProd a lower hLower) |>.congr ?_
    intro x
    rfl
  exact ((summable_prod_of_nonneg
    (f := fun x : (ℕ × ℕ) × ℕ =>
      padicLogPowerMajorantTerm a lower x.2 x.1)
    (fun x => padicLogPowerMajorantTerm_nonneg a lower x.2 x.1)).1 hswap).1 mn

private def selbergEulerCorrectionLogPowerMajorant (k : ℕ) (mn : ℕ × ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) *
    ∑' p : ℕ, padicLogPowerMajorantTerm r (k - r) p mn

private theorem selbergEulerCorrectionLogPowerMajorant_nonneg
    (k : ℕ) (mn : ℕ × ℕ) :
    0 ≤ selbergEulerCorrectionLogPowerMajorant k mn := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (by positivity)
    (tsum_nonneg fun p => padicLogPowerMajorantTerm_nonneg r (k - r) p mn)

private theorem summable_selbergEulerCorrectionLogPowerMajorant
    (k : ℕ)
    (hLower : ∀ r ∈ Finset.range (k + 1),
      Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionLogPowerCoeff (k - r) mn.1 mn.2|)) :
    Summable (selbergEulerCorrectionLogPowerMajorant k) := by
  unfold selbergEulerCorrectionLogPowerMajorant
  have hfinite : ∀ s : Finset ℕ,
      (∀ r ∈ s, r ∈ Finset.range (k + 1)) →
      Summable (fun mn : ℕ × ℕ =>
        ∑ r ∈ s, (k.choose r : ℝ) *
          ∑' p : ℕ, padicLogPowerMajorantTerm r (k - r) p mn) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact summable_zero
    | @insert r s hrs ih =>
        have hrange : r ∈ Finset.range (k + 1) := hs r (by simp)
        have hsRange : ∀ q ∈ s, q ∈ Finset.range (k + 1) := by
          intro q hq
          exact hs q (by simp [hq])
        have hrSummable := (summable_padicLogPowerMajorantSum r (k - r)
          (hLower r hrange)).mul_left (k.choose r : ℝ)
        simpa [Finset.sum_insert, hrs] using hrSummable.add (ih hsRange)
  exact hfinite (Finset.range (k + 1)) (fun _ h => h)

private theorem abs_selbergEulerCorrectionLogPowerCoeff_succ_le
    (k : ℕ)
    (hLower : ∀ r ∈ Finset.range (k + 1),
      Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionLogPowerCoeff (k - r) mn.1 mn.2|))
    (mn : ℕ × ℕ) :
    |selbergEulerCorrectionLogPowerCoeff (k + 1) mn.1 mn.2| ≤
      selbergEulerCorrectionLogPowerMajorant k mn := by
  rcases mn with ⟨m, n⟩
  rcases m.eq_zero_or_pos with rfl | hm
  · simpa [selbergEulerCorrectionLogPowerCoeff] using
      selbergEulerCorrectionLogPowerMajorant_nonneg k (0, n)
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa [selbergEulerCorrectionLogPowerCoeff] using
      selbergEulerCorrectionLogPowerMajorant_nonneg k (m, 0)
  rw [selbergEulerCorrectionLogPowerCoeff_succ_eq k m n hm hn]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun p hp =>
    Finset.abs_sum_le_sum_abs _ _) ?_
  rw [selbergEulerCorrectionLogPowerMajorant, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r hr
  calc
    (∑ p ∈ (m * n).primeFactors,
        |(k.choose r : ℝ) *
          selbergCorrectionLogPowerLocal (r + 1) p
            (m.factorization p) (n.factorization p) *
          selbergEulerCorrectionLogPowerCoeff (k - r)
            (m / p ^ m.factorization p) (n / p ^ n.factorization p)|) ≤
      ∑ p ∈ (m * n).primeFactors,
        (k.choose r : ℝ) * padicLogPowerMajorantTerm r (k - r) p (m, n) := by
      apply Finset.sum_le_sum
      intro p hp
      have hchoose : (0 : ℝ) ≤ k.choose r := by exact_mod_cast Nat.zero_le (k.choose r)
      rw [abs_mul, abs_mul,
        abs_of_nonneg hchoose]
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hmul :
          |selbergCorrectionLogPowerLocal (r + 1) p
              (m.factorization p) (n.factorization p)| *
            |selbergEulerCorrectionLogPowerCoeff (k - r)
              (m / p ^ m.factorization p) (n / p ^ n.factorization p)| ≤
          selbergCorrectionLogPowerMajorant (r + 1) p
              (m.factorization p) (n.factorization p) *
            |selbergEulerCorrectionLogPowerCoeff (k - r)
              (m / p ^ m.factorization p) (n / p ^ n.factorization p)| :=
        mul_le_mul_of_nonneg_right
          (abs_selbergCorrectionLogPowerLocal_le (r + 1) hprime.two_le
            (m.factorization p) (n.factorization p))
          (abs_nonneg _)
      have hout := mul_le_mul_of_nonneg_left hmul hchoose
      simpa [padicLogPowerMajorantTerm, mul_assoc] using hout
    _ = (k.choose r : ℝ) *
        ∑ p ∈ (m * n).primeFactors,
          padicLogPowerMajorantTerm r (k - r) p (m, n) := by
      rw [Finset.mul_sum]
    _ ≤ (k.choose r : ℝ) *
        ∑' p : ℕ, padicLogPowerMajorantTerm r (k - r) p (m, n) := by
      refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast Nat.zero_le (k.choose r))
      exact (summable_padicLogPowerMajorantTerm_fixed r (k - r)
        (hLower r hr) (m, n)).sum_le_tsum (m * n).primeFactors
          (fun q _ => padicLogPowerMajorantTerm_nonneg r (k - r) q (m, n))

/-- Every ordinary logarithmic derivative of the global correction is absolutely summable. -/
theorem summable_abs_selbergEulerCorrectionLogPowerCoeff (k : ℕ) :
    Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionLogPowerCoeff k mn.1 mn.2|) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · simpa [selbergEulerCorrectionLogPowerCoeff_zero] using
          summable_abs_selbergEulerCorrectionCoeff
      · have hLower : ∀ r ∈ Finset.range (k + 1),
            Summable (fun mn : ℕ × ℕ =>
              |selbergEulerCorrectionLogPowerCoeff (k - r) mn.1 mn.2|) := by
          intro r hr
          apply ih
          omega
        exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
          (abs_selbergEulerCorrectionLogPowerCoeff_succ_le k hLower)
          (summable_selbergEulerCorrectionLogPowerMajorant k hLower)

end

end RHTower.Sieve
