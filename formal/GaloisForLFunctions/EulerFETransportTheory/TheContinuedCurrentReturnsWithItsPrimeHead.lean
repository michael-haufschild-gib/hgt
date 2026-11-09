import GaloisForLFunctions.EulerFETransportTheory.TheContinuedCurrentRetainsTheRoughVariance
import GaloisForLFunctions.HTGeometry.PrimeSeparatedDeterminantCoefficient
import Mathlib.Algebra.Field.GeomSum

/-!
# Joint prime-phase returns of the continued rough current

Finite geometric probes concentrate any prescribed finite prime phases.
Their exact phase-error means and the conditioned infinite rough variance
produce arbitrarily high returns of the actual continued Euler current.
-/

open Complex Filter Topology MeasureTheory RHTower XiAtlasFinitePart
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

private theorem mean_limit_of_bounded_error (J : ℝ → ℝ) (D C : ℝ)
    (hbound : ∀ T : ℝ, |J T - T * D| ≤ C) :
    Tendsto (fun T : ℝ => J T / T) atTop (𝓝 D) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  refine ⟨max 1 ((|C| + 1) / ε), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hlarge : |C| + 1 ≤ ε * T := by
    have hh := (le_max_right _ _).trans hT
    rw [div_le_iff₀ hε] at hh
    linarith only [hh]
  have he : J T / T - D = (J T - T * D) / T := by field_simp
  rw [Real.dist_eq, he, abs_div, abs_of_pos hT0]
  refine (div_le_div_of_nonneg_right (hbound T) hT0.le).trans_lt ?_
  rw [div_lt_iff₀ hT0]
  linarith only [hlarge, le_abs_self C]

private theorem smooth_head_dyadic_mean {Y : ℕ} (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ n ∈ S, n ∈ Nat.smoothNumbers Y) :
    Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖integerHeightPoly S w t‖ ^ 2) / T)
      atTop (𝓝 (∑ n ∈ S, ‖w n‖ ^ 2)) := by
  let D : ℝ := ∑ n ∈ S, ‖w n‖ ^ 2
  let C : ℝ := 4 * ((S.sup (id : ℕ → ℕ) : ℕ) : ℝ) *
    (1 + Real.log (S.sup (id : ℕ → ℕ) : ℕ)) * D
  have hb : ∀ T : ℝ, |(∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2) - T * D| ≤ C :=
    fun T => norm_integral_normSq_head_sub_diag_le T hS
      (fun n hn => Finset.le_sup (f := (id : ℕ → ℕ)) hn)
  have hc : Continuous (fun t : ℝ => ‖integerHeightPoly S w t‖ ^ 2) :=
    (continuous_integerHeightPoly S w).norm.pow 2
  apply mean_limit_of_bounded_error _ _ (2 * C)
  intro T
  have h2 : IntervalIntegrable (fun t : ℝ => ‖integerHeightPoly S w t‖ ^ 2)
      volume 0 (2 * T) := hc.intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t : ℝ => ‖integerHeightPoly S w t‖ ^ 2)
      volume 0 T := hc.intervalIntegrable _ _
  rw [← intervalIntegral.integral_interval_sub_left h2 h1]
  have he : (∫ t in (0 : ℝ)..(2 * T), ‖integerHeightPoly S w t‖ ^ 2) -
      (∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2) - T * D =
    ((∫ t in (0 : ℝ)..(2 * T), ‖integerHeightPoly S w t‖ ^ 2) - (2 * T) * D) -
    ((∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2) - T * D) := by ring
  change |(∫ t in (0 : ℝ)..(2 * T), ‖integerHeightPoly S w t‖ ^ 2) -
    (∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2) - T * D| ≤ _
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hb (2 * T), hb T])

private theorem family_as_smooth_head {κ : Type*} [Fintype κ] [DecidableEq κ]
    (k : κ → ℕ) (a : κ → ℂ) (hk : Function.Injective k)
    {Y : ℕ} (hY : ∀ i, k i ∈ Nat.smoothNumbers Y) :
    ∃ (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ n ∈ S, n ∈ Nat.smoothNumbers Y) ∧
      (∀ t : ℝ, integerHeightPoly S w t = familyHeightPoly Finset.univ k a t) ∧
      (∑ n ∈ S, ‖w n‖ ^ 2) = ∑ i, ‖a i‖ ^ 2 := by
  classical
  let S := Finset.univ.image k
  let w : ℕ → ℂ := Function.extend k a (fun _ => 0)
  have hw : ∀ i, w (k i) = a i := hk.extend_apply a (fun _ => 0)
  refine ⟨S, w, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact hY i
  · intro t
    unfold integerHeightPoly familyHeightPoly
    dsimp only [S]
    rw [Finset.sum_image (fun i _ j _ he => hk he)]
    simp only [id_eq, hw]
  · dsimp only [S]
    rw [Finset.sum_image (fun i _ j _ he => hk he)]
    simp only [hw]

section PrimePacket
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def packetIndex (q : ι → Nat.Primes) (E : ι → Finset ℕ)
    (v : ∀ i, ↥(E i)) : ℕ := ∏ i, (q i : ℕ) ^ (v i : ℕ)

private theorem packetIndex_injective (q : ι → Nat.Primes) (hq : Function.Injective q)
    (E : ι → Finset ℕ) : Function.Injective (packetIndex q E) := by
  intro v w he
  have hh := HTGeometry.primePacket_powProduct_injective q hq he
  funext i
  exact Subtype.ext (congrFun hh i)

omit [DecidableEq ι] in
private theorem packetIndex_smooth (q : ι → Nat.Primes) (E : ι → Finset ℕ)
    {Y : ℕ} (hqY : ∀ i, (q i : ℕ) < Y) (v : ∀ i, ↥(E i)) :
    packetIndex q E v ∈ Nat.smoothNumbers Y := by
  apply Nat.mem_smoothNumbers'.mpr
  intro p hp hpd
  obtain ⟨i, _, hi⟩ := hp.prime.exists_mem_finset_dvd hpd
  have he : p = (q i : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hp (q i).2).mp (hp.dvd_of_dvd_pow hi)
  simpa only [he] using hqY i

/-- A product of finite polynomials in distinct prime phases. -/
def primePacketPolynomial (q : ι → Nat.Primes) (E : ι → Finset ℕ)
    (c : ι → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∏ i, ∑ k ∈ E i, c i k * Complex.exp (((t * (k * Real.log (q i : ℕ)) : ℝ) : ℂ) * I)

private theorem packetPolynomial_eq_family (q : ι → Nat.Primes) (E : ι → Finset ℕ)
    (c : ι → ℕ → ℂ) (t : ℝ) :
    primePacketPolynomial q E c t =
      familyHeightPoly Finset.univ (packetIndex q E) (fun v => ∏ i, c i (v i)) t := by
  have hprod : primePacketPolynomial q E c t =
      ∏ i, ∑ k : ↥(E i), c i k * Complex.exp (((t * (k * Real.log (q i : ℕ)) : ℝ) : ℂ) * I) := by
    unfold primePacketPolynomial
    apply Finset.prod_congr rfl
    intro i _
    exact (Finset.sum_coe_sort (E i) _).symm
  rw [hprod, Fintype.prod_sum, familyHeightPoly]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  have hl : Real.log (packetIndex q E v) = ∑ i, (v i : ℕ) * Real.log (q i : ℕ) := by
    rw [packetIndex, Nat.cast_prod, Real.log_prod]
    · simp only [Nat.cast_pow, Real.log_pow]
    · intro i _
      exact_mod_cast pow_ne_zero (v i : ℕ) (q i).2.ne_zero
  rw [hl, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]

private theorem packet_energy (E : ι → Finset ℕ) (c : ι → ℕ → ℂ) :
    (∑ v : ∀ i, ↥(E i), ‖∏ i, c i (v i)‖ ^ 2) =
      ∏ i, ∑ k ∈ E i, ‖c i k‖ ^ 2 := by
  calc
    _ = ∑ v : ∀ i, ↥(E i), ∏ i, ‖c i (v i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [norm_prod, ← Finset.prod_pow]
    _ = ∏ i, ∑ k : ↥(E i), ‖c i k‖ ^ 2 :=
      (Fintype.prod_sum (fun i (k : ↥(E i)) => ‖c i k‖ ^ 2)).symm
    _ = _ := Finset.prod_congr rfl fun i _ =>
      Finset.sum_coe_sort (E i) (fun n : ℕ => ‖c i n‖ ^ 2)

private theorem packet_as_smooth_head (q : ι → Nat.Primes) (hq : Function.Injective q)
    (E : ι → Finset ℕ) (c : ι → ℕ → ℂ) {Y : ℕ} (hqY : ∀ i, (q i : ℕ) < Y) :
    ∃ (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ n ∈ S, n ∈ Nat.smoothNumbers Y) ∧
      (∀ t : ℝ, integerHeightPoly S w t = primePacketPolynomial q E c t) ∧
      (∑ n ∈ S, ‖w n‖ ^ 2) = ∏ i, ∑ k ∈ E i, ‖c i k‖ ^ 2 := by
  obtain ⟨S, w, hS, he, hm⟩ := family_as_smooth_head (packetIndex q E)
    (fun v => ∏ i, c i (v i)) (packetIndex_injective q hq E) (packetIndex_smooth q E hqY)
  exact ⟨S, w, hS, fun t => (he t).trans (packetPolynomial_eq_family q E c t).symm,
    hm.trans (packet_energy E c)⟩

/-- Distinct prime coordinates give the exact product energy on dyadic windows. -/
theorem tendsto_primePacketPolynomial_mean (q : ι → Nat.Primes) (hq : Function.Injective q)
    (E : ι → Finset ℕ) (c : ι → ℕ → ℂ) :
    Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖primePacketPolynomial q E c t‖ ^ 2) / T)
      atTop (𝓝 (∏ i, ∑ k ∈ E i, ‖c i k‖ ^ 2)) := by
  let Y := Finset.univ.sup (fun i => (q i : ℕ)) + 1
  have hqY : ∀ i, (q i : ℕ) < Y := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j : ι => (q j : ℕ)) (Finset.mem_univ i))
  obtain ⟨S, w, hS, he, hm⟩ := packet_as_smooth_head q hq E c hqY
  simpa only [he, hm] using smooth_head_dyadic_mean S w hS

end PrimePacket

/-- The positive height phase of a prime. -/
def primeHeightPhase (p : Nat.Primes) (t : ℝ) : ℂ :=
  Complex.exp (((t * Real.log (p : ℕ) : ℝ) : ℂ) * I)

private theorem prime_phase_pow (p : Nat.Primes) (t : ℝ) (n : ℕ) :
    Complex.exp (((t * (n * Real.log (p : ℕ)) : ℝ) : ℂ) * I) =
      primeHeightPhase p t ^ n := by
  rw [primeHeightPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem circle_mul_conj (a : Circle) :
    (a : ℂ) * (starRingEnd ℂ) (a : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
  norm_num

private theorem phase_geometric_boundary (a : Circle) (z : ℂ) (k : ℕ) :
    (z - (a : ℂ)) * (∑ n ∈ Finset.range (k + 1), ((starRingEnd ℂ) (a : ℂ) * z) ^ n) =
      -(a : ℂ) + ((a : ℂ) * ((starRingEnd ℂ) (a : ℂ)) ^ (k + 1)) * z ^ (k + 1) := by
  have he : z - (a : ℂ) = (a : ℂ) * ((starRingEnd ℂ) (a : ℂ) * z - 1) := by
    rw [mul_sub, ← mul_assoc, circle_mul_conj, one_mul, mul_one]
  rw [he, mul_assoc, mul_geom_sum, mul_pow]
  ring

section PhaseBox
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A geometric box probe for prescribed unit prime phases. -/
def primePhaseBox (q : ι → Nat.Primes) (α : ι → Circle) (k : ℕ) : ℝ → ℂ :=
  primePacketPolynomial q (fun _ => Finset.range (k + 1))
    (fun i n => ((starRingEnd ℂ) (α i : ℂ)) ^ n)

omit [DecidableEq ι] in
private theorem phaseBox_energy (α : ι → Circle) (k : ℕ) :
    (∏ i, ∑ n ∈ Finset.range (k + 1), ‖((starRingEnd ℂ) (α i : ℂ)) ^ n‖ ^ 2) =
      ((k + 1 : ℕ) : ℝ) ^ Fintype.card ι := by
  simp only [norm_pow, Complex.norm_conj, Circle.norm_coe, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ]

private theorem phaseBox_as_head (q : ι → Nat.Primes) (hq : Function.Injective q)
    (α : ι → Circle) (k : ℕ) {Y : ℕ} (hqY : ∀ i, (q i : ℕ) < Y) :
    ∃ (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ n ∈ S, n ∈ Nat.smoothNumbers Y) ∧
      (∀ t : ℝ, integerHeightPoly S w t = primePhaseBox q α k t) ∧
      (∑ n ∈ S, ‖w n‖ ^ 2) = ((k + 1 : ℕ) : ℝ) ^ Fintype.card ι := by
  obtain ⟨S, w, hS, he, hm⟩ := packet_as_smooth_head q hq
    (fun _ => Finset.range (k + 1)) (fun i n => ((starRingEnd ℂ) (α i : ℂ)) ^ n) hqY
  exact ⟨S, w, hS, he, hm.trans (phaseBox_energy α k)⟩

private theorem phaseBox_mean (q : ι → Nat.Primes) (hq : Function.Injective q)
    (α : ι → Circle) (k : ℕ) :
    Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖primePhaseBox q α k t‖ ^ 2) / T)
      atTop (𝓝 (((k + 1 : ℕ) : ℝ) ^ Fintype.card ι)) := by
  simpa only [primePhaseBox, phaseBox_energy] using tendsto_primePacketPolynomial_mean q hq
    (fun _ => Finset.range (k + 1)) (fun i n => ((starRingEnd ℂ) (α i : ℂ)) ^ n)

private def boundaryExponents (k : ℕ) (j : ι) : ι → Finset ℕ :=
  Function.update (fun _ => Finset.range (k + 1)) j {0, k + 1}

private def boundaryCoefficients (α : ι → Circle) (k : ℕ) (j : ι) : ι → ℕ → ℂ :=
  Function.update (fun i n => ((starRingEnd ℂ) (α i : ℂ)) ^ n) j
    (fun n => if n = 0 then -(α j : ℂ) else
      (α j : ℂ) * ((starRingEnd ℂ) (α j : ℂ)) ^ (k + 1))

private theorem phaseBox_boundary_identity (q : ι → Nat.Primes) (α : ι → Circle)
    (k : ℕ) (j : ι) (t : ℝ) :
    primePacketPolynomial q (boundaryExponents k j) (boundaryCoefficients α k j) t =
      (primeHeightPhase (q j) t - (α j : ℂ)) * primePhaseBox q α k t := by
  let f : ι → ℂ := fun i => ∑ n ∈ Finset.range (k + 1),
    (((starRingEnd ℂ) (α i : ℂ)) * primeHeightPhase (q i) t) ^ n
  have hmain : primePhaseBox q α k t = ∏ i, f i := by
    unfold primePhaseBox primePacketPolynomial
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro n _
    rw [prime_phase_pow, mul_pow]
  have hlocal : (fun i => ∑ n ∈ boundaryExponents k j i,
      boundaryCoefficients α k j i n *
        Complex.exp (((t * (n * Real.log (q i : ℕ)) : ℝ) : ℂ) * I)) =
    Function.update f j ((primeHeightPhase (q j) t - (α j : ℂ)) * f j) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp only [boundaryExponents, boundaryCoefficients, Function.update_self]
      rw [Finset.sum_pair (Ne.symm (Nat.succ_ne_zero k))]
      simp only [prime_phase_pow, pow_zero, mul_one,
        if_neg (Nat.succ_ne_zero k)]
      exact (phase_geometric_boundary (α j) (primeHeightPhase (q j) t) k).symm
    · simp only [boundaryExponents, boundaryCoefficients, Function.update_of_ne hi]
      dsimp only [f]
      apply Finset.sum_congr rfl
      intro n _
      rw [prime_phase_pow, mul_pow]
  rw [primePacketPolynomial, hlocal, Finset.prod_update_of_mem (Finset.mem_univ j), hmain]
  rw [Finset.sdiff_singleton_eq_erase, mul_assoc,
    Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]

omit [Fintype ι] in
private theorem norm_boundaryCoefficients (α : ι → Circle) (k : ℕ) (j i : ι) (n : ℕ) :
    ‖boundaryCoefficients α k j i n‖ = 1 := by
  by_cases hi : i = j
  · subst i
    simp only [boundaryCoefficients, Function.update_self]
    split_ifs <;> simp only [norm_neg, norm_mul, norm_pow, Complex.norm_conj,
      Circle.norm_coe, one_pow, mul_one]
  · simp only [boundaryCoefficients, Function.update_of_ne hi, norm_pow,
      Complex.norm_conj, Circle.norm_coe, one_pow]

private theorem phaseBox_boundary_energy (α : ι → Circle) (k : ℕ) (j : ι) :
    (∏ i, ∑ n ∈ boundaryExponents k j i, ‖boundaryCoefficients α k j i n‖ ^ 2) =
      (2 / ((k + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ Fintype.card ι := by
  have hlocal : (fun i => ∑ n ∈ boundaryExponents k j i,
      ‖boundaryCoefficients α k j i n‖ ^ 2) =
    Function.update (fun _ : ι => ((k + 1 : ℕ) : ℝ)) j 2 := by
    funext i
    simp only [norm_boundaryCoefficients, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases hi : i = j
    · subst i
      simp only [boundaryExponents, Function.update_self,
        Finset.card_pair (Ne.symm (Nat.succ_ne_zero k)), Nat.cast_ofNat]
    · simp only [boundaryExponents, Function.update_of_ne hi, Finset.card_range]
  rw [hlocal, Finset.prod_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
  have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hprod := Finset.mul_prod_erase Finset.univ
    (fun _ : ι => ((k + 1 : ℕ) : ℝ)) (Finset.mem_univ j)
  have hprod' : ((k + 1 : ℕ) : ℝ) *
      (∏ _i ∈ Finset.univ.erase j, ((k + 1 : ℕ) : ℝ)) =
      ((k + 1 : ℕ) : ℝ) ^ Fintype.card ι := by
    simpa only [Finset.prod_const, Finset.card_univ] using hprod
  rw [← hprod']
  field_simp

/-- A geometric box pays exactly `2/(k+1)` of its mass for each prescribed
prime-phase error, independently of the number of other prime coordinates. -/
theorem tendsto_primePhaseBox_phase_error_mean (q : ι → Nat.Primes)
    (hq : Function.Injective q) (α : ι → Circle) (k : ℕ) (j : ι) :
    Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖primePhaseBox q α k t‖ ^ 2 *
      ‖primeHeightPhase (q j) t - (α j : ℂ)‖ ^ 2) / T) atTop
      (𝓝 ((2 / ((k + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ Fintype.card ι)) := by
  have hm := tendsto_primePacketPolynomial_mean q hq
    (boundaryExponents k j) (boundaryCoefficients α k j)
  simpa only [phaseBox_boundary_identity, phaseBox_boundary_energy, norm_mul, mul_pow,
    mul_comm] using hm

end PhaseBox

private theorem continuous_clipped_current {σ H : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hregular : ∀ t : ℝ, H ≤ t → riemannZeta ((σ : ℂ) + t * I) ≠ 0) (Y : ℕ) :
    Continuous (fun t : ℝ => logDeriv riemannZeta ((σ : ℂ) + (max H t : ℝ) * I) +
      smallPrimeEulerCurrent Y ((σ : ℂ) + (max H t : ℝ) * I)) := by
  have hmax : Continuous (fun t : ℝ => max H t) := continuous_const.max continuous_id
  have hline : Continuous (fun t : ℝ => (σ : ℂ) + (max H t : ℝ) * I) := by fun_prop
  have hlog : Continuous (fun t : ℝ => logDeriv riemannZeta
      ((σ : ℂ) + (max H t : ℝ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz1 : (σ : ℂ) + (max H t : ℝ) * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      have hre : ((σ : ℂ) + (max H t : ℝ) * I).re = σ := by simp
      rw [hre, Complex.one_re] at hr
      linarith only [hr, hσ1]
    have ha := RHTower.analyticAt_riemannZeta hz1
    have hc : ContinuousAt (logDeriv riemannZeta) ((σ : ℂ) + (max H t : ℝ) * I) :=
      (ha.deriv.div ha (hregular (max H t) (le_max_left _ _))).continuousAt
    exact hc.comp (f := fun u : ℝ => (σ : ℂ) + (max H u : ℝ) * I)
      (x := t) hline.continuousAt
  have hsmall : Continuous (fun t : ℝ => smallPrimeEulerCurrent Y ((σ : ℂ) + t * I)) := by
    have he : (fun t : ℝ => smallPrimeEulerCurrent Y ((σ : ℂ) + t * I)) =
        PhaseSeries.phaseSeries (smallPrimeVonMangoldtCoeff Y σ) := by
      funext t
      rw [← smallPrime_heightSeries_eq_eulerCurrent Y hσ t, integerHeightSeries, neg_neg]
    rw [he]
    exact PhaseSeries.continuous_phaseSeries (smallPrimeVonMangoldtCoeff_zero Y σ)
      (summable_norm_smallPrimeVonMangoldtCoeff Y hσ)
  exact hlog.add (hsmall.comp hmax)

private theorem eventually_exists_joint_phase_good {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℕ) (f : ℝ → ℂ) (hf : Continuous f) (A : ℝ) (hA : 0 ≤ A)
    (hm : ∀ (S : Finset ℕ) (w : ℕ → ℂ), (∀ n ∈ S, n ∈ Nat.smoothNumbers Y) →
      Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖integerHeightPoly S w t‖ ^ 2 * ‖f t‖ ^ 2) / T)
        atTop (𝓝 ((∑ n ∈ S, ‖w n‖ ^ 2) * A)))
    (q : ι → Nat.Primes) (hq : Function.Injective q) (hqY : ∀ i, (q i : ℕ) < Y)
    (α : ι → Circle) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∃ t ∈ Set.Icc T (2 * T),
      (∀ i, ‖primeHeightPhase (q i) t - (α i : ℂ)‖ < η) ∧ ‖f t‖ ^ 2 < A + δ := by
  classical
  let C := A + δ
  have hC : 0 < C := by dsimp [C]; linarith only [hA, hδ]
  let lam := C / η ^ 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * lam * Fintype.card ι / δ)
  let N : ℝ := (k + 1 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hphase : lam * ((Fintype.card ι : ℝ) * (2 / N)) < δ := by
    have hh : 2 * lam * Fintype.card ι < δ * k := by
      have hh := (div_lt_iff₀ hδ).mp hk
      linarith only [hh]
    rw [show lam * ((Fintype.card ι : ℝ) * (2 / N)) =
      (2 * lam * Fintype.card ι) / N by ring, div_lt_iff₀ hN]
    dsimp [N]
    push_cast
    linarith only [hh, hδ]
  let R := primePhaseBox q α k
  let D : ℝ := N ^ Fintype.card ι
  have hD : 0 < D := pow_pos hN _
  obtain ⟨S, w, hS, he, hmass⟩ := phaseBox_as_head q hq α k hqY
  have hR : Continuous R := by
    have he' : integerHeightPoly S w = R := funext he
    rw [← he']
    exact continuous_integerHeightPoly S w
  have hRmean : Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖R t‖ ^ 2) / T)
      atTop (𝓝 D) := phaseBox_mean q hq α k
  have hFmean : Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖R t‖ ^ 2 * ‖f t‖ ^ 2) / T)
      atTop (𝓝 (D * A)) := by
    simpa only [he, hmass] using hm S w hS
  let E : ι → ℝ → ℝ := fun i t => ‖primeHeightPhase (q i) t - (α i : ℂ)‖ ^ 2
  have hE : ∀ i, Continuous (E i) := by
    intro i
    dsimp [E, primeHeightPhase]
    fun_prop
  have hEmean : ∀ i, Tendsto (fun T : ℝ =>
      (∫ t in T..(2 * T), ‖R t‖ ^ 2 * E i t) / T) atTop (𝓝 ((2 / N) * D)) :=
    fun i => tendsto_primePhaseBox_phase_error_mean q hq α k i
  let cost : ℝ → ℝ := fun t => ‖f t‖ ^ 2 + lam * ∑ i, E i t
  have hcost : Continuous cost := (hf.norm.pow 2).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => hE i))
  let L : ℝ := D * A + lam * ∑ _i : ι, (2 / N) * D
  have hCostMean : Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖R t‖ ^ 2 * cost t) / T)
      atTop (𝓝 L) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hEmean i)
    have hlim := hFmean.add (hsum.const_mul lam)
    refine hlim.congr' (Filter.Eventually.of_forall fun T => ?_)
    have heq : (fun t => ‖R t‖ ^ 2 * cost t) =
        (fun t => ‖R t‖ ^ 2 * ‖f t‖ ^ 2 + lam * ∑ i, ‖R t‖ ^ 2 * E i t) := by
      funext t
      dsimp only [cost]
      rw [mul_add, mul_left_comm (‖R t‖ ^ 2) lam, Finset.mul_sum]
    have hri : IntervalIntegrable (fun t => ‖R t‖ ^ 2 * ‖f t‖ ^ 2) volume T (2 * T) :=
      ((hR.norm.pow 2).mul (hf.norm.pow 2)).intervalIntegrable _ _
    have hsi : IntervalIntegrable (fun t => lam * ∑ i, ‖R t‖ ^ 2 * E i t) volume T (2 * T) :=
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (hR.norm.pow 2).mul (hE i))).intervalIntegrable _ _
    have hei : ∀ i, IntervalIntegrable (fun t => ‖R t‖ ^ 2 * E i t) volume T (2 * T) :=
      fun i => ((hR.norm.pow 2).mul (hE i)).intervalIntegrable _ _
    rw [heq]
    dsimp only
    rw [intervalIntegral.integral_add hri hsi,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => hei i),
      add_div, mul_div_assoc, Finset.sum_div]
  have hLC : L < C * D := by
    have hp := mul_lt_mul_of_pos_right hphase hD
    dsimp [L, C]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith only [hp]
  have hgap := (hCostMean.sub (hRmean.const_mul C)).eventually
    (eventually_lt_nhds (by linarith only [hLC] : L - C * D < 0))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgap] with T hT0 hneg
  have hex : ∃ t ∈ Set.Icc T (2 * T), cost t < C := by
    by_contra h
    push Not at h
    have hleft : IntervalIntegrable (fun t => C * ‖R t‖ ^ 2) volume T (2 * T) :=
      (continuous_const.mul (hR.norm.pow 2)).intervalIntegrable _ _
    have hright : IntervalIntegrable (fun t => ‖R t‖ ^ 2 * cost t) volume T (2 * T) :=
      ((hR.norm.pow 2).mul hcost).intervalIntegrable _ _
    have hi := intervalIntegral.integral_mono_on (by linarith only [hT0] : T ≤ 2 * T)
      hleft hright
      (fun t ht => by
        have hh := mul_le_mul_of_nonneg_left (h t ht) (sq_nonneg ‖R t‖)
        simpa only [mul_comm C] using hh)
    rw [intervalIntegral.integral_const_mul] at hi
    have hd := div_le_div_of_nonneg_right hi hT0.le
    rw [mul_div_assoc] at hd
    linarith only [hd, hneg]
  obtain ⟨t, ht, hct⟩ := hex
  have hsum0 : 0 ≤ ∑ i, E i t := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfsmall : ‖f t‖ ^ 2 < C := by
    have hp := mul_nonneg hlam.le hsum0
    dsimp only [cost] at hct
    linarith only [hct, hp]
  refine ⟨t, ht, fun i => ?_, hfsmall⟩
  have hi : E i t ≤ ∑ j, E j t :=
    Finset.single_le_sum (f := fun j => E j t)
      (fun j _ => sq_nonneg ‖primeHeightPhase (q j) t - (α j : ℂ)‖) (Finset.mem_univ i)
  have hmul : lam * E i t < C := by
    have hh := mul_le_mul_of_nonneg_left hi hlam.le
    have hf0 := sq_nonneg ‖f t‖
    dsimp only [cost] at hct
    linarith only [hh, hf0, hct]
  have hCeq : C = lam * η ^ 2 := by dsimp [lam]; field_simp
  rw [hCeq] at hmul
  have he : E i t < η ^ 2 := by nlinarith only [hmul, hlam]
  dsimp only [E] at he
  nlinarith only [he, hη, norm_nonneg (primeHeightPhase (q i) t - (α i : ℂ))]

/-- Every sufficiently high dyadic window contains a prescribed finite prime
phase return where the full continued rough current lies below its exact
variance threshold with any positive slack. -/
theorem not_asymptoticAbscissaLaw_has_dyadic_primePhase_returns
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ H : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < H ∧
      (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      (∀ t : ℝ, H ≤ t → riemannZeta ((σ : ℂ) + t * I) ≠ 0) ∧
      ∀ (Y : ℕ) (P : Finset Nat.Primes) (α : Nat.Primes → Circle),
        (∀ p ∈ P, (p : ℕ) < Y) → ∀ η δ : ℝ, 0 < η → 0 < δ →
          ∀ᶠ T : ℝ in atTop, ∃ t ∈ Set.Icc T (2 * T),
            (∀ p ∈ P, ‖primeHeightPhase p t - (α p : ℂ)‖ < η) ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + t * I) +
              smallPrimeEulerCurrent Y ((σ : ℂ) + t * I)‖ ^ 2 <
                (∑' n : ℕ, ‖roughVonMangoldtCoeff Y σ n‖ ^ 2) + δ := by
  classical
  obtain ⟨σ, H, hσ, hσ1, hH, hq, hregular, hm⟩ :=
    not_asymptoticAbscissaLaw_has_conditioned_roughMean hnot
  refine ⟨σ, H, hσ, hσ1, hH, hq, hregular, fun Y P α hP η δ hη hδ => ?_⟩
  let f : ℝ → ℂ := fun t => logDeriv riemannZeta ((σ : ℂ) + (max H t : ℝ) * I) +
    smallPrimeEulerCurrent Y ((σ : ℂ) + (max H t : ℝ) * I)
  have hf : Continuous f := continuous_clipped_current (by linarith only [hσ]) hσ1 hregular Y
  let A : ℝ := ∑' n : ℕ, ‖roughVonMangoldtCoeff Y σ n‖ ^ 2
  have hA : 0 ≤ A := tsum_nonneg fun _ => sq_nonneg _
  have hm' : ∀ (S : Finset ℕ) (w : ℕ → ℂ), (∀ n ∈ S, n ∈ Nat.smoothNumbers Y) →
      Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖integerHeightPoly S w t‖ ^ 2 * ‖f t‖ ^ 2) / T)
        atTop (𝓝 ((∑ n ∈ S, ‖w n‖ ^ 2) * A)) := by
    intro S w hS
    refine (hm Y S w hS).congr' ?_
    filter_upwards [eventually_ge_atTop H] with T hT
    apply congrArg (fun u : ℝ => u / T)
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith only [hH, hT] : T ≤ 2 * T)] at ht
    have htH : H ≤ t := hT.trans ht.1
    simp only [f, max_eq_right htH]
  have hgood := eventually_exists_joint_phase_good Y f hf A hA hm'
    (fun p : ↥P => (p : Nat.Primes)) Subtype.val_injective
    (fun p => hP p p.property) (fun p : ↥P => α p) hη hδ
  filter_upwards [hgood, eventually_ge_atTop H] with T hgood hT
  obtain ⟨t, ht, hph, hval⟩ := hgood
  have htH : H ≤ t := hT.trans ht.1
  refine ⟨t, ht, fun p hp => hph ⟨p, hp⟩, ?_⟩
  simpa only [f, max_eq_right htH] using hval

/-- Arbitrary finite prime phases recur at unbounded heights together with
the actual continued rough current at its variance threshold. -/
theorem not_asymptoticAbscissaLaw_has_joint_primePhase_returns
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ H : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < H ∧
      (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      (∀ t : ℝ, H ≤ t → riemannZeta ((σ : ℂ) + t * I) ≠ 0) ∧
      ∀ (Y : ℕ) (P : Finset Nat.Primes) (α : Nat.Primes → Circle),
        (∀ p ∈ P, (p : ℕ) < Y) → ∀ η δ : ℝ, 0 < η → 0 < δ → ∀ B : ℝ,
          ∃ t : ℝ, B < t ∧
            (∀ p ∈ P, ‖primeHeightPhase p t - (α p : ℂ)‖ < η) ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + t * I) +
              smallPrimeEulerCurrent Y ((σ : ℂ) + t * I)‖ ^ 2 <
                (∑' n : ℕ, ‖roughVonMangoldtCoeff Y σ n‖ ^ 2) + δ := by
  obtain ⟨σ, H, hσ, hσ1, hH, hq, hregular, hr⟩ :=
    not_asymptoticAbscissaLaw_has_dyadic_primePhase_returns hnot
  refine ⟨σ, H, hσ, hσ1, hH, hq, hregular, fun Y P α hP η δ hη hδ B => ?_⟩
  obtain ⟨T, hTB, t, ht, hph, hval⟩ :=
    ((eventually_gt_atTop B).and (hr Y P α hP η δ hη hδ)).exists
  exact ⟨t, hTB.trans_le ht.1, hph, hval⟩

#print axioms tendsto_primePacketPolynomial_mean
#print axioms tendsto_primePhaseBox_phase_error_mean
#print axioms not_asymptoticAbscissaLaw_has_dyadic_primePhase_returns
#print axioms not_asymptoticAbscissaLaw_has_joint_primePhase_returns

end GaloisForLFunctions.EulerFETransportTheory
