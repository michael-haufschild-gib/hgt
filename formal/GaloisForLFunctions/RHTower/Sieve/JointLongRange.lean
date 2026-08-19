import GaloisForLFunctions.RHTower.Sieve.FreeEtaLadder
import GaloisForLFunctions.RHTower.Sieve.RoughRemainderLimit
import GaloisForLFunctions.RHTower.Sieve.ShortIntervalLength
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# The long designated range at its own ratio

The long ladder's defect forces `η_Q ≤ (log x)^{a−b−1−β/2}`, which the corpus's
`ladderEta b (a/b) x = (log x)^{a−b−5/4}` meets only for `β ≤ 1/2`.  This module rebuilds the long
range on `Sieve/FreeEtaLadder` at

```text
   η_Q = (log x)^{a−b−2} ,
   Q   = primes in ( siftStart a x , gLadderTop (siftStart a x) η_Q (cardLength b x) ] .
```

The harmonic mass is unaffected by the change of ratio — it depends only on the two endpoints —
which is exactly why the ratio was free to be shrunk.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The long ladder's ratio. -/
def jointLongEta (a b x : ℝ) : ℝ := (Real.log x) ^ (a - b - 2)

theorem jointLongEta_pos {a b x : ℝ} (hx : 1 < x) : 0 < jointLongEta a b x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

/-- The long designated range's top, at the free ratio. -/
def jointLongTopF (a b x : ℝ) : ℕ :=
  gLadderTop ((siftStart a x : ℕ) : ℝ) (jointLongEta a b x) (cardLength b x)

/-- The long designated range, at the free ratio. -/
def jointLongSetF (a b x : ℝ) : Finset ℕ := primesRange (siftStart a x) (jointLongTopF a b x)

theorem siftStart_pos (c x : ℝ) : (0 : ℝ) < ((siftStart c x : ℕ) : ℝ) := by
  have h : 1 ≤ siftStart c x := Nat.one_le_ceil_iff.2 (Real.exp_pos _)
  have h1 : (1 : ℝ) ≤ ((siftStart c x : ℕ) : ℝ) := by exact_mod_cast h
  linarith

/-- **The long base lies below the long ladder's target, eventually.** -/
theorem eventually_siftStart_le_cardLength {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, ((siftStart a x : ℕ) : ℝ) ≤ cardLength b x := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha0).comp Real.tendsto_log_atTop
  have hpowba : Tendsto (fun x : ℝ => (Real.log x) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hba).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    hpowa.eventually_ge_atTop (1 : ℝ), hpowba.eventually_ge_atTop (2 : ℝ)]
    with x hlog1 hpa1 hpba2
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hsplit : (Real.log x) ^ b = (Real.log x) ^ a * (Real.log x) ^ (b - a) := by
    rw [← Real.rpow_add hlog0]
    ring_nf
  have hgap : (Real.log x) ^ a + 1 ≤ (Real.log x) ^ b := by
    rw [hsplit]
    nlinarith [hpa1, hpba2]
  have hceil : ((siftStart a x : ℕ) : ℝ) ≤ Real.exp ((Real.log x) ^ a) + 1 := by
    rw [siftStart]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos _).le)
  have hone : (1 : ℝ) ≤ Real.exp ((Real.log x) ^ a) := Real.one_le_exp (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hstep : Real.exp ((Real.log x) ^ a) + 1 ≤ Real.exp ((Real.log x) ^ b) := by
    have hmono : Real.exp ((Real.log x) ^ a + 1) ≤ Real.exp ((Real.log x) ^ b) :=
      Real.exp_le_exp.2 hgap
    rw [Real.exp_add] at hmono
    nlinarith [hmono, hone, he2, Real.exp_pos ((Real.log x) ^ a)]
  rw [cardLength]
  linarith [hceil, hstep]

/-- **The long ladder does not overshoot its target.** -/
theorem jointLongTopF_le {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, ((jointLongTopF a b x : ℕ) : ℝ) ≤ cardLength b x := by
  filter_upwards [eventually_siftStart_le_cardLength ha0 hab,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hle hx1
  exact (gLadderTop_bounds (siftStart_pos a x) hle (jointLongEta_pos hx1)).1

/-- **The long ladder reaches within one step of its target.** -/
theorem jointLongTopF_ge {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop,
      cardLength b x / (1 + jointLongEta a b x) - 1 ≤ ((jointLongTopF a b x : ℕ) : ℝ) := by
  filter_upwards [eventually_siftStart_le_cardLength ha0 hab,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hle hx1
  exact (gLadderTop_bounds (siftStart_pos a x) hle (jointLongEta_pos hx1)).2

theorem jointLongSetF_prime (a b x : ℝ) : ∀ q ∈ jointLongSetF a b x, q.Prime := fun _ hq =>
  (mem_primesRange.1 hq).1

theorem jointLongSetF_ge (a b x : ℝ) :
    ∀ q ∈ jointLongSetF a b x, ((siftStart a x : ℕ) : ℝ) ≤ (q : ℝ) := by
  intro q hq
  exact_mod_cast (mem_primesRange.1 hq).2.1.le

/-- **The long designated set is covered by its ladder.** -/
theorem jointLongSetF_range {a b x : ℝ} (hx : 1 < x) :
    ∀ q ∈ jointLongSetF a b x,
      ((siftStart a x : ℕ) : ℝ) < (q : ℝ)
        ∧ (q : ℝ) ≤ ((siftStart a x : ℕ) : ℝ) * (1 + jointLongEta a b x)
            ^ (gLadderSteps ((siftStart a x : ℕ) : ℝ) (jointLongEta a b x) (cardLength b x)) := by
  intro q hq
  obtain ⟨-, hlo, hhi⟩ := mem_primesRange.1 hq
  refine ⟨by exact_mod_cast hlo, ?_⟩
  have hη := jointLongEta_pos (a := a) (b := b) hx
  have hfl : ((jointLongTopF a b x : ℕ) : ℝ)
      ≤ ((siftStart a x : ℕ) : ℝ) * (1 + jointLongEta a b x)
          ^ (gLadderSteps ((siftStart a x : ℕ) : ℝ) (jointLongEta a b x) (cardLength b x)) := by
    rw [jointLongTopF, gLadderTop]
    refine Nat.floor_le ?_
    have h1 : (0 : ℝ) < ((siftStart a x : ℕ) : ℝ) := siftStart_pos a x
    positivity
  have hqc : (q : ℝ) ≤ ((jointLongTopF a b x : ℕ) : ℝ) := by exact_mod_cast hhi
  linarith

/-! ## The harmonic mass at the free ratio -/

/-- The long ladder's ratio vanishes. -/
theorem tendsto_jointLongEta {a b : ℝ} (hab : a < b) :
    Tendsto (fun x : ℝ => jointLongEta a b x) atTop (𝓝 0) := by
  have hneg : a - b - 2 < 0 := by linarith
  have h := (tendsto_rpow_neg_atTop (y := -(a - b - 2)) (by linarith)).comp
    Real.tendsto_log_atTop
  refine h.congr fun x => ?_
  rw [Function.comp_apply, jointLongEta, neg_neg]

/-- **The long top is at least a quarter of its target, eventually.** -/
theorem eventually_jointLongTopF_ge_quarter {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, cardLength b x / 4 ≤ ((jointLongTopF a b x : ℕ) : ℝ) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hpowb : Tendsto (fun x : ℝ => (Real.log x) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb0).comp Real.tendsto_log_atTop
  filter_upwards [jointLongTopF_ge ha0 hab,
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) (tendsto_jointLongEta hab),
    hpowb.eventually_ge_atTop (Real.log 8),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hge hη1 hpb hx1
  have hcl : Real.exp (Real.log 8) ≤ cardLength b x := by
    rw [cardLength]
    exact Real.exp_le_exp.2 hpb
  have h8 : (8 : ℝ) ≤ cardLength b x := by
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 8)] at hcl
  have hden : (0 : ℝ) < 1 + jointLongEta a b x := by
    have := jointLongEta_pos (a := a) (b := b) hx1
    linarith
  have hhalf : cardLength b x / 2 ≤ cardLength b x / (1 + jointLongEta a b x) := by
    refine div_le_div_of_nonneg_left (cardLength_pos b x).le hden (by linarith)
  linarith [hge, hhalf, h8]

/-- **The long range's harmonic mass grows, at the free ratio.** -/
theorem tendsto_jointLongMassF {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ => mertensS (jointLongTopF a b x) - mertensS (siftStart a x))
      atTop atTop := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hba : (0 : ℝ) < b - a := by linarith
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha0).comp Real.tendsto_log_atTop
  have hpowb : Tendsto (fun x : ℝ => (Real.log x) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb0).comp Real.tendsto_log_atTop
  have hminor : Tendsto (fun x : ℝ =>
      (b - a) * Real.log (Real.log x) - Real.log 4 + ladderMassConst) atTop atTop := by
    have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have h1 : Tendsto (fun x : ℝ => (b - a) * Real.log (Real.log x)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hba hloglog
    exact Filter.tendsto_atTop_add_const_right atTop (-Real.log 4 + ladderMassConst) h1 |>.congr
      fun x => by ring
  refine tendsto_atTop_mono' _ ?_ hminor
  filter_upwards [eventually_jointLongTopF_ge_quarter ha0 hab, eventually_le_siftStart ha0 2,
    log_siftStart_le ha0, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    hpowa.eventually_ge_atTop (Real.log 2), hpowb.eventually_ge_atTop (2 * Real.log 4),
    hpowa.eventually_ge_atTop (1 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)]
    with x hq h2s hls hlog1 hpa2 hpb4 hpa1 hx1
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hclq : cardLength b x / 4 ≤ ((jointLongTopF a b x : ℕ) : ℝ) := hq
  have hcl : cardLength b x = Real.exp ((Real.log x) ^ b) := rfl
  -- the top is at least 2
  have hcl8 : (8 : ℝ) ≤ cardLength b x := by
    rw [hcl]
    have : Real.exp (Real.log 8) ≤ Real.exp ((Real.log x) ^ b) := by
      refine Real.exp_le_exp.2 ?_
      have h4 : Real.log 8 ≤ 2 * Real.log 4 := by
        have h1 : Real.log 8 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
        have h2 : Real.log 16 = 2 * Real.log 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
          push_cast; ring
        linarith
      linarith
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 8)] at this
  have htop2 : 2 ≤ jointLongTopF a b x := by
    have : (2 : ℝ) ≤ ((jointLongTopF a b x : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  -- the mass, from Mertens
  have hmass := gLadderMass_ge htop2 h2s
  -- the two logarithms
  have hlogtop : (Real.log x) ^ b - Real.log 4 ≤ Real.log ((jointLongTopF a b x : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < cardLength b x / 4 := by
      have := cardLength_pos b x; positivity
    have hle := Real.log_le_log hpos hclq
    rw [Real.log_div (ne_of_gt (cardLength_pos b x)) (by norm_num), hcl, Real.log_exp] at hle
    linarith
  have hlogtop2 : (Real.log x) ^ b / 2 ≤ Real.log ((jointLongTopF a b x : ℕ) : ℝ) := by
    linarith [hlogtop, hpb4]
  have hlogsift : Real.log ((siftStart a x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ a := by
    linarith [hls, hpa2]
  have hlogsift0 : (0 : ℝ) < Real.log ((siftStart a x : ℕ) : ℝ) := by
    have := log_siftStart_ge a x
    linarith [hpa1]
  have hb2pos : (0 : ℝ) < (Real.log x) ^ b / 2 := by
    have : (0 : ℝ) < (Real.log x) ^ b := Real.rpow_pos_of_pos hlog0 b
    linarith
  have hL1 : Real.log ((Real.log x) ^ b / 2)
      ≤ Real.log (Real.log ((jointLongTopF a b x : ℕ) : ℝ)) :=
    Real.log_le_log hb2pos hlogtop2
  have hL2 : Real.log (Real.log ((siftStart a x : ℕ) : ℝ)) ≤ Real.log (2 * (Real.log x) ^ a) :=
    Real.log_le_log hlogsift0 hlogsift
  have hval1 : Real.log ((Real.log x) ^ b / 2) = b * Real.log (Real.log x) - Real.log 2 := by
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hlog0 b)) (by norm_num),
      Real.log_rpow hlog0]
  have hval2 : Real.log (2 * (Real.log x) ^ a) = Real.log 2 + a * Real.log (Real.log x) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hlog0 a)),
      Real.log_rpow hlog0]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  linarith [hmass, hL1, hL2, hval1.le, hval1.ge, hval2.le, hval2.ge, hlog4.le, hlog4.ge]

/-- **The long ladder's base lies below its top, eventually.** -/
theorem eventually_siftStart_le_jointLongTopF {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, siftStart a x ≤ jointLongTopF a b x := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha0).comp Real.tendsto_log_atTop
  have hpowba : Tendsto (fun x : ℝ => (Real.log x) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hba).comp Real.tendsto_log_atTop
  filter_upwards [eventually_jointLongTopF_ge_quarter ha0 hab,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    hpowa.eventually_ge_atTop (4 : ℝ), hpowba.eventually_ge_atTop (2 : ℝ)]
    with x hq hlog1 hpa4 hpba2
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hsplit : (Real.log x) ^ b = (Real.log x) ^ a * (Real.log x) ^ (b - a) := by
    rw [← Real.rpow_add hlog0]
    ring_nf
  have hgap : (Real.log x) ^ a + 4 ≤ (Real.log x) ^ b := by
    rw [hsplit]; nlinarith [hpa4, hpba2]
  set E : ℝ := Real.exp ((Real.log x) ^ a) with hE
  have hE5 : (5 : ℝ) ≤ E := by
    have := Real.add_one_le_exp ((Real.log x) ^ a)
    rw [← hE] at this
    linarith
  have hexp4 : (5 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hgrow : E * 5 ≤ Real.exp ((Real.log x) ^ b) := by
    have h1 : Real.exp ((Real.log x) ^ a + 4) ≤ Real.exp ((Real.log x) ^ b) :=
      Real.exp_le_exp.2 hgap
    rw [Real.exp_add, ← hE] at h1
    nlinarith [h1, hexp4, Real.exp_pos ((Real.log x) ^ a)]
  have hceil : ((siftStart a x : ℕ) : ℝ) ≤ E + 1 := by
    rw [siftStart, ← hE]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos _).le)
  have hcl : cardLength b x = Real.exp ((Real.log x) ^ b) := rfl
  have hfin : ((siftStart a x : ℕ) : ℝ) ≤ cardLength b x / 4 := by
    rw [hcl, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [hceil, hgrow, hE5]
  have : ((siftStart a x : ℕ) : ℝ) ≤ ((jointLongTopF a b x : ℕ) : ℝ) := le_trans hfin hq
  exact_mod_cast this

end

end RHTower.Sieve
