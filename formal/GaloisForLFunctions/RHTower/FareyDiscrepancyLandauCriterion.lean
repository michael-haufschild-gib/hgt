import GaloisForLFunctions.RHTower.Sieve.FareySet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood

/-!
# Farey discrepancy and the Riemann hypothesis (Landau's receiver)

Let `F_n` be the Farey fractions `a/q`, `1 ≤ a ≤ q ≤ n`, `(a, q) = 1`, listed in increasing order
`f_1 < ⋯ < f_L`.  The Farey discrepancy is `δ_ν = f_ν - ν/L`.  If
`Σ_ν |δ_ν| = O(n^{1/2+ε})` for every `ε > 0`, the Riemann hypothesis holds.

The Ramanujan sums `Σ_{(a,q)=1} e(a/q) = μ(q)` give `Σ_ν e(f_ν) = M(n)`, the Mertens function,
while `Σ_ν e(ν/L) = 0` for `L ≥ 2`.  Since `|e(x) - e(y)| ≤ 2π|x - y|`,
`|M(n)| ≤ 2π Σ_ν |δ_ν|`, and Littlewood's criterion applies.
-/

open Finset Filter Topology
open RHTower.Sieve (fareySet mem_fareySet fareySet_eq_biUnion)

namespace RHTower

noncomputable section

/-- The value `a/q` of a Farey pair `(a, q)`. -/
def fareyValue (p : ℕ × ℕ) : ℝ := (p.1 : ℝ) / (p.2 : ℝ)

/-- The rank of a Farey fraction: the number of Farey fractions of order `n` not exceeding it. -/
def fareyRank (n : ℕ) (p : ℕ × ℕ) : ℕ :=
  ((fareySet n).filter (fun r => fareyValue r ≤ fareyValue p)).card

/-- Landau's Farey discrepancy `Σ_ν |f_ν - ν/L|`. -/
def fareyL1Discrepancy (n : ℕ) : ℝ :=
  ∑ p ∈ fareySet n, |fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)|

/-- Reduced fractions are determined by their values. -/
theorem fareyValue_injOn (n : ℕ) : Set.InjOn fareyValue (fareySet n : Set (ℕ × ℕ)) := by
  intro p hp r hr hpr
  obtain ⟨⟨ha1, _⟩, ⟨hq1, _⟩, _, hcop⟩ := mem_fareySet.mp hp
  obtain ⟨⟨hb1, _⟩, ⟨hr1, _⟩, _, hcop'⟩ := mem_fareySet.mp hr
  unfold fareyValue at hpr
  have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
  have hr0 : (0 : ℝ) < r.2 := by exact_mod_cast hr1
  have hcross : p.1 * r.2 = r.1 * p.2 := by
    rw [div_eq_div_iff hq0.ne' hr0.ne'] at hpr
    exact_mod_cast hpr
  have h1 : p.2 ∣ r.2 := by
    have : p.2 ∣ p.1 * r.2 := ⟨r.1, by rw [hcross]; ring⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have h2 : r.2 ∣ p.2 := by
    have : r.2 ∣ r.1 * p.2 := ⟨p.1, by rw [← hcross]; ring⟩
    exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
  have h3 : p.2 = r.2 := Nat.dvd_antisymm h1 h2
  have h4 : p.1 = r.1 := by
    rw [h3] at hcross
    exact Nat.eq_of_mul_eq_mul_right (by omega) hcross
  exact Prod.ext h4 h3

/-- **Ranks enumerate a finite set of reals.**  For a finite `V ⊆ ℝ`,
`Σ_{w ∈ V} g(#{u ∈ V : u ≤ w}) = Σ_{k < |V|} g(k + 1)`. -/
theorem sum_card_filter_le_eq_sum_range (V : Finset ℝ) (g : ℕ → ℂ) :
    ∑ w ∈ V, g ((V.filter (fun u => u ≤ w)).card) = ∑ k ∈ range V.card, g (k + 1) := by
  induction V using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hmax a h)
    rw [sum_insert ha, card_insert_of_notMem ha, Finset.sum_range_succ (fun k => g (k + 1))]
    have h1 : ((insert a s).filter (fun u => u ≤ a)).card = s.card + 1 := by
      rw [filter_insert, if_pos le_rfl, card_insert_of_notMem (by simp [ha])]
      congr 1
      rw [filter_true_of_mem fun x hx => (hmax x hx).le]
    have h2 : ∀ w ∈ s, ((insert a s).filter (fun u => u ≤ w)).card
        = (s.filter (fun u => u ≤ w)).card := by
      intro w hw
      rw [filter_insert, if_neg (not_le.mpr (hmax w hw))]
    rw [h1, sum_congr rfl fun w hw => by rw [h2 w hw], ih]
    ring

/-- **The rank sum.**  `Σ_{p ∈ F_n} g(rank p) = Σ_{k < L} g(k + 1)`. -/
theorem sum_fareyRank_eq_sum_range (n : ℕ) (g : ℕ → ℂ) :
    ∑ p ∈ fareySet n, g (fareyRank n p) = ∑ k ∈ range (fareySet n).card, g (k + 1) := by
  set V := (fareySet n).image fareyValue with hV
  have hinj := fareyValue_injOn n
  have hcard : V.card = (fareySet n).card := card_image_of_injOn hinj
  have hrank : ∀ p ∈ fareySet n, fareyRank n p = (V.filter (fun u => u ≤ fareyValue p)).card := by
    intro p _
    unfold fareyRank
    rw [hV, filter_image]
    exact (card_image_of_injOn (hinj.mono (filter_subset _ _))).symm
  rw [sum_congr rfl fun p hp => by rw [hrank p hp],
    ← sum_image (f := fun w => g ((V.filter (fun u => u ≤ w)).card)) hinj, ← hV,
    sum_card_filter_le_eq_sum_range, hcard]

/-- `Σ_{k < L} e((k + 1)/L) = 0` for `L ≥ 2`. -/
theorem sum_range_exp_succ_div_eq_zero {L : ℕ} (hL : 2 ≤ L) :
    ∑ k ∈ range L, Complex.exp (2 * Real.pi * Complex.I * ((k + 1 : ℕ) : ℂ) / L) = 0 := by
  have hL0 : L ≠ 0 := by omega
  set ζ := Complex.exp (2 * Real.pi * Complex.I / L) with hζ
  have hprim : IsPrimitiveRoot ζ L := Complex.isPrimitiveRoot_exp L hL0
  have hterm : ∀ k ∈ range L, Complex.exp (2 * Real.pi * Complex.I * ((k + 1 : ℕ) : ℂ) / L)
      = ζ * ζ ^ k := by
    intro k _
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl hterm, ← mul_sum, hprim.geom_sum_eq_zero (by omega), mul_zero]

/-- **Ramanujan's sum at `1`.**  `Σ_{1 ≤ a ≤ q, (a,q) = 1} e(a/q) = μ(q)` for `q ≥ 1`. -/
theorem sum_coprime_exp_eq_moebius {q : ℕ} (hq : 1 ≤ q) :
    ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / q)
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  set Q : CGLPositiveModulus := ⟨q, by omega⟩ with hQ
  have hram := cglRamanujanAdditiveSum_natCast_eq_gcd_mobiusDivisorSum Q 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, sum_singleton, Nat.cast_one, one_mul,
    Nat.div_one] at hram
  rw [← hram]
  unfold cglRamanujanAdditiveSum
  haveI : NeZero q := ⟨by omega⟩
  refine sum_nbij' (fun a : ℕ => (a : ZMod q))
    (fun u : ZMod q => if u.val = 0 then q else u.val) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha
    simp only [mem_filter, mem_univ, true_and]
    exact (ZMod.isUnit_iff_coprime a q).mpr ha.2
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    simp only [mem_filter, mem_Icc]
    have hcop : Nat.Coprime u.val q := by
      have := (ZMod.isUnit_iff_coprime u.val q).mp (by rwa [ZMod.natCast_zmod_val])
      exact this
    split_ifs with h0
    · refine ⟨⟨hq, le_rfl⟩, ?_⟩
      rw [h0] at hcop
      have : q = 1 := by simpa using hcop
      rw [this]; exact Nat.coprime_one_left 1
    · exact ⟨⟨Nat.one_le_iff_ne_zero.mpr h0, (ZMod.val_lt u).le⟩, hcop⟩
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha
    simp only [ZMod.val_natCast]
    by_cases haq : a = q
    · subst haq; simp
    · have : a < q := lt_of_le_of_ne ha.1.2 haq
      rw [Nat.mod_eq_of_lt this, if_neg (by omega)]
  · intro u _
    split_ifs with h0
    · rw [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero u).mp h0).symm
    · exact ZMod.natCast_zmod_val u
  · intro a _
    rw [mul_one, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]

/-- **The Farey exponential sum is the Mertens function.**  `Σ_{p ∈ F_n} e(a/q) = M(n)`. -/
theorem sum_fareySet_exp_eq_mertens (n : ℕ) :
    ∑ p ∈ fareySet n, Complex.exp (2 * Real.pi * Complex.I * (fareyValue p : ℂ))
      = mobiusMertensPartialSum n := by
  rw [fareySet_eq_biUnion, sum_biUnion]
  · have h1 : ∀ q ∈ Icc 1 n, ∑ p ∈ ((Icc 1 q).filter (fun a => Nat.Coprime a q)).image
          (fun a => (a, q)), Complex.exp (2 * Real.pi * Complex.I * (fareyValue p : ℂ))
        = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
      intro q hq
      rw [sum_image (fun a _ b _ hab => by simpa using hab)]
      rw [← sum_coprime_exp_eq_moebius (mem_Icc.mp hq).1]
      refine sum_congr rfl fun a _ => ?_
      unfold fareyValue
      push_cast
      ring_nf
    rw [sum_congr rfl h1]
    unfold mobiusMertensPartialSum mobiusComplexCoefficient
    rw [range_eq_Ico, ← Ico_add_one_right_eq_Icc]
    rw [show Ico 0 (n + 1) = insert 0 (Ico 1 (n + 1)) by
      ext k; simp only [mem_insert, mem_Ico]; omega, sum_insert (by simp)]
    simp
  · intro q _ r _ hqr
    simp only [Function.onFun]
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_image] at hp hp'
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨b, _, hb⟩ := hp'
    exact hqr (congrArg Prod.snd hb).symm


/-- `‖e(α) - e(β)‖ ≤ 2π|α - β|` for real `α, β`. -/
theorem norm_exp_two_pi_I_sub_le (α β : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (β : ℂ))‖ ≤ 2 * Real.pi * |α - β| := by
  have e : Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))
      - Complex.exp (2 * Real.pi * Complex.I * (β : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (β : ℂ))
        * (Complex.exp (Complex.I * ((2 * Real.pi * (α - β) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul]
  have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (β : ℂ))‖ = 1 := by
    rw [show 2 * Real.pi * Complex.I * (β : ℂ) = ((2 * Real.pi * β : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem two_le_card_fareySet {n : ℕ} (hn : 2 ≤ n) : 2 ≤ (fareySet n).card := by
  have h1 : ((1 : ℕ), (1 : ℕ)) ∈ fareySet n := mem_fareySet.mpr
    ⟨⟨le_rfl, by omega⟩, ⟨le_rfl, by omega⟩, le_rfl, Nat.coprime_one_left 1⟩
  have h2 : ((1 : ℕ), (2 : ℕ)) ∈ fareySet n := mem_fareySet.mpr
    ⟨⟨le_rfl, by omega⟩, ⟨by norm_num, hn⟩, by norm_num, Nat.coprime_one_left 2⟩
  have hsub : ({((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (2 : ℕ))} : Finset (ℕ × ℕ)) ⊆ fareySet n := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact h1
    · exact h2
  have := card_le_card hsub
  rwa [card_pair (by simp)] at this

/-- **Landau's inequality.**  `|M(n)| ≤ 2π Σ_ν |f_ν - ν/L|` for `n ≥ 2`. -/
theorem norm_mobiusMertensPartialSum_le_fareyL1Discrepancy {n : ℕ} (hn : 2 ≤ n) :
    ‖mobiusMertensPartialSum n‖ ≤ 2 * Real.pi * fareyL1Discrepancy n := by
  set L := (fareySet n).card with hL
  have hL2 := two_le_card_fareySet hn
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hzero : ∑ p ∈ fareySet n,
      Complex.exp (2 * Real.pi * Complex.I * (((fareyRank n p : ℝ) / L : ℝ) : ℂ)) = 0 := by
    have h1 := sum_fareyRank_eq_sum_range n
      (fun k => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / L))
    have h2 : ∀ p ∈ fareySet n,
        Complex.exp (2 * Real.pi * Complex.I * (((fareyRank n p : ℝ) / L : ℝ) : ℂ))
          = Complex.exp (2 * Real.pi * Complex.I * ((fareyRank n p : ℕ) : ℂ) / L) := by
      intro p _
      congr 1
      push_cast
      ring
    rw [sum_congr rfl h2, h1, ← hL]
    exact sum_range_exp_succ_div_eq_zero hL2
  have hM := sum_fareySet_exp_eq_mertens n
  have hdiff : mobiusMertensPartialSum n
      = ∑ p ∈ fareySet n, (Complex.exp (2 * Real.pi * Complex.I * (fareyValue p : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (((fareyRank n p : ℝ) / L : ℝ) : ℂ))) := by
    rw [sum_sub_distrib, hzero, sub_zero, hM]
  rw [hdiff, fareyL1Discrepancy, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
  exact norm_exp_two_pi_I_sub_le _ _

/-- **Landau's Farey receiver.**  If `Σ_ν |f_ν - ν/L| = O(n^{1/2+δ})` for every `δ > 0`, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_fareyL1Discrepancy_le
    (h : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) :
    RiemannHypothesis := by
  refine mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis.mp fun δ hδ => ?_
  obtain ⟨C, hC0, hC⟩ := h δ hδ
  refine ⟨max (2 * Real.pi * C) 2, le_trans (by norm_num) (le_max_right _ _), fun N => ?_⟩
  have hpow : 1 ≤ ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) :=
    Real.one_le_rpow (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]) (by linarith)
  rcases lt_or_ge N 2 with hN | hN
  · have hsmall : ‖mobiusMertensPartialSum N‖ ≤ 2 := by
      unfold mobiusMertensPartialSum mobiusComplexCoefficient
      interval_cases N
      · simp
      · simp [Finset.sum_range_succ]
    calc ‖mobiusMertensPartialSum N‖ ≤ 2 := hsmall
      _ ≤ 2 * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by linarith
      _ ≤ max (2 * Real.pi * C) 2 * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · calc ‖mobiusMertensPartialSum N‖ ≤ 2 * Real.pi * fareyL1Discrepancy N :=
          norm_mobiusMertensPartialSum_le_fareyL1Discrepancy hN
      _ ≤ 2 * Real.pi * (C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) :=
          mul_le_mul_of_nonneg_left (hC N) (by positivity)
      _ = 2 * Real.pi * C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by ring
      _ ≤ max (2 * Real.pi * C) 2 * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end

end RHTower
