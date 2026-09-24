import Mathlib

/-!
# All-shift polarity of complete Möbius lcm fibres

For two literal source cells `k,m`, the complete signed divisor-pair fibre at
`lcm(d,e)=n` is `μ(n)` if `n ∣ k*m`, and zero otherwise. The same identity
survives any finite window and any real weight external to the divisor pair.
It does not cover the divisor-dependent discrepancy weights in EDQ's physical
cross fibre, nor estimate the remaining sum across distinct lcm labels or the
incomplete high-lcm cutoff boundary.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

private theorem sum_mu_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, moebius d) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.one_apply] using h

private theorem sum_mu_common (q k : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ k then moebius d else 0) =
      if Nat.Coprime q k then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hset : q.divisors.filter (fun d => d ∣ k) = (Nat.gcd q k).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdk⟩
      exact ⟨Nat.dvd_gcd hdq hdk, by positivity⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_left q k), hq.ne'⟩,
        hdg.trans (Nat.gcd_dvd_right q k)⟩
  rw [hset, sum_mu_divisors]

private theorem sum_mu_common_real (q k : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ k then ((moebius d : ℤ) : ℝ) else 0) =
      if Nat.Coprime q k then 1 else 0 := by
  exact_mod_cast sum_mu_common q k hq

/-- Complete signed lcm fibre at two literal source cells. -/
def shiftedLcmFibre (n k m : ℕ) : ℝ :=
  ∑ de ∈ (n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = n),
    (if de.1 ∣ k then ((moebius de.1 : ℤ) : ℝ) else 0) *
      (if de.2 ∣ m then ((moebius de.2 : ℤ) : ℝ) else 0)

private theorem divisor_sum_shiftedLcmFibre (n k m : ℕ) (hn : 0 < n) :
    (∑ q ∈ n.divisors, shiftedLcmFibre q k m) =
      (∑ d ∈ n.divisors, if d ∣ k then ((moebius d : ℤ) : ℝ) else 0) *
      (∑ e ∈ n.divisors, if e ∣ m then ((moebius e : ℤ) : ℝ) else 0) := by
  classical
  unfold shiftedLcmFibre
  have hmem : ∀ (q : ℕ) (de : ℕ × ℕ),
      q ∈ n.divisors ∧
          de ∈ (q.divisors ×ˢ q.divisors).filter (fun de => Nat.lcm de.1 de.2 = q) ↔
        q ∈ n.divisors.filter (fun q => Nat.lcm de.1 de.2 = q) ∧
          de ∈ n.divisors ×ˢ n.divisors := by
    intro q de
    constructor
    · rintro ⟨hq, hde⟩
      obtain ⟨hdeq, hlcm⟩ := Finset.mem_filter.mp hde
      obtain ⟨hd, he⟩ := Finset.mem_product.mp hdeq
      refine ⟨Finset.mem_filter.mpr ⟨hq, hlcm⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.dvd_of_mem_divisors hq), hn.ne'⟩
      · exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors he).trans (Nat.dvd_of_mem_divisors hq), hn.ne'⟩
    · rintro ⟨hq, hde⟩
      obtain ⟨hqdiv, hlcm⟩ := Finset.mem_filter.mp hq
      obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
      have hq0 : q ≠ 0 := (Nat.pos_of_mem_divisors hqdiv).ne'
      refine ⟨hqdiv, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hlcm⟩⟩
      · exact Nat.mem_divisors.mpr ⟨by simpa [hlcm] using Nat.dvd_lcm_left de.1 de.2, hq0⟩
      · exact Nat.mem_divisors.mpr ⟨by simpa [hlcm] using Nat.dvd_lcm_right de.1 de.2, hq0⟩
  rw [Finset.sum_comm' hmem]
  have hinner : ∀ de ∈ n.divisors ×ˢ n.divisors,
      (∑ q ∈ n.divisors.filter (fun q => Nat.lcm de.1 de.2 = q),
        (if de.1 ∣ k then ((moebius de.1 : ℤ) : ℝ) else 0) *
          (if de.2 ∣ m then ((moebius de.2 : ℤ) : ℝ) else 0)) =
        (if de.1 ∣ k then ((moebius de.1 : ℤ) : ℝ) else 0) *
          (if de.2 ∣ m then ((moebius de.2 : ℤ) : ℝ) else 0) := by
    intro de hde
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    have hqdiv : Nat.lcm de.1 de.2 ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd)
        (Nat.dvd_of_mem_divisors he), hn.ne'⟩
    have hfilter : n.divisors.filter (fun q => Nat.lcm de.1 de.2 = q) =
        {Nat.lcm de.1 de.2} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hq⟩
        exact hq.symm
      · intro hq
        subst q
        exact ⟨hqdiv, rfl⟩
    rw [hfilter, Finset.sum_singleton]
  rw [Finset.sum_congr rfl hinner, Finset.sum_product]
  simpa only [Prod.fst, Prod.snd] using
    (Finset.sum_mul_sum n.divisors n.divisors
      (fun d => if d ∣ k then ((moebius d : ℤ) : ℝ) else 0)
      (fun e => if e ∣ m then ((moebius e : ℤ) : ℝ) else 0)).symm

/-- All-shift lcm polarity: shift affects support, never sign within a complete fibre. -/
theorem shiftedLcmFibre_eq_moebius_indicator (n k m : ℕ) (hn : 0 < n) :
    shiftedLcmFibre n k m =
      if n ∣ k * m then ((moebius n : ℤ) : ℝ) else 0 := by
  let f : ℕ → ℝ := fun q => if q ∣ k * m then ((moebius q : ℤ) : ℝ) else 0
  let g : ℕ → ℝ := fun q => if Nat.Coprime q (k * m) then 1 else 0
  have hf : ∀ q > 0, (∑ d ∈ q.divisors, shiftedLcmFibre d k m) = g q := by
    intro q hq
    rw [divisor_sum_shiftedLcmFibre q k m hq,
      sum_mu_common_real q k hq, sum_mu_common_real q m hq]
    dsimp [g]
    rw [ite_zero_mul_ite_zero]
    simp only [one_mul, Nat.coprime_mul_iff_right]
  have hg : ∀ q > 0, (∑ d ∈ q.divisors, f d) = g q := by
    intro q hq
    exact sum_mu_common_real q (k * m) hq
  have hfinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun q => shiftedLcmFibre q k m) (g := g)).mp hf n hn
  have hginv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := g)).mp hg n hn
  exact (hfinv.symm.trans hginv)

/-- The complete all-shift polarity survives any finite window and divisor-independent weight. -/
theorem weighted_shiftedLcmFibre_eq_moebius_incidence
    (S : Finset ℕ) (w : ℕ → ℝ) (n h : ℕ) (hn : 0 < n) :
    (∑ k ∈ S, w k * shiftedLcmFibre n k (k + h)) =
      ((moebius n : ℤ) : ℝ) *
        ∑ k ∈ S.filter (fun k => n ∣ k * (k + h)), w k := by
  calc
    _ = ∑ k ∈ S, w k *
          (if n ∣ k * (k + h) then ((moebius n : ℤ) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [shiftedLcmFibre_eq_moebius_indicator n k (k + h) hn]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : n ∣ k * (k + h) <;> simp [hk, mul_comm]

/-- Premise-free polarity, including the empty zero-lcm fibre. -/
theorem shiftedLcmFibre_eq_moebius_indicator_all (n k m : ℕ) :
    shiftedLcmFibre n k m =
      if n ∣ k * m then ((moebius n : ℤ) : ℝ) else 0 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [shiftedLcmFibre]
  · exact shiftedLcmFibre_eq_moebius_indicator n k m hn

/-- Premise-free weighted-window polarity at every lcm label. -/
theorem weighted_shiftedLcmFibre_eq_moebius_incidence_all
    (S : Finset ℕ) (w : ℕ → ℝ) (n h : ℕ) :
    (∑ k ∈ S, w k * shiftedLcmFibre n k (k + h)) =
      ((moebius n : ℤ) : ℝ) *
        ∑ k ∈ S.filter (fun k => n ∣ k * (k + h)), w k := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [shiftedLcmFibre]
  · exact weighted_shiftedLcmFibre_eq_moebius_incidence S w n h hn

end RHTower
